import OMAStatements.S_oeis_a006697
import Mathlib

/-!
We count right-special factors, which admit two different next letters.
The substitution is handled through its finite blocks, whose two copies
in the next block give the two possible right extensions.
-/

open List

namespace OMA.A006697

open OMA.S_oeis_a006697 (σ w)

private def zeros (k : ℕ) : List Bool := List.replicate k false

private def block : ℕ → List Bool
  | 0 => [true]
  | k + 1 => block k ++ block k ++ [false]

private theorem map_append (u v : List Bool) : σ (u ++ v) = σ u ++ σ v := by
  simp [σ, List.flatMap_append]

private theorem step_block (k : ℕ) : σ (block k) = block (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [block, map_append, ih]
    rfl

private theorem iterate_block (k : ℕ) : σ^[k] [true] = block k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, step_block]

private theorem block_prefix_succ (k : ℕ) : block k <+: block (k+1) :=
  ⟨block k ++ [false], by simp [block, List.append_assoc]⟩

private theorem block_prefix {k j : ℕ} (h : k ≤ j) : block k <+: block j :=
  Nat.le_induction (by simp : block k <+: block k) (fun j _ hj => hj.trans (block_prefix_succ j)) j h

private theorem block_length (k : ℕ) : (block k).length + 1 = 2 ^ (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 + 1 = (k+1)+1 by rfl, pow_succ]
    simp only [block, List.length_append, List.length_singleton]
    omega

private theorem block_long (k : ℕ) : k < (block k).length := by
  induction k with
  | zero => decide
  | succ k ih => simp only [block, List.length_append, List.length_singleton]; omega

private theorem block_first (k : ℕ) : ∃ t, block k = true :: t := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t ++ block k ++ [false], by simp only [block, ht, List.cons_append]⟩

private theorem occurrence_append {a : Bool} {pre post u v : List Bool}
    (h : pre ++ (a :: post) = u ++ v) :
      (∃ r, u = pre ++ (a :: r) ∧ post = r ++ v) ∨
      (∃ l, pre = u ++ l ∧ v = l ++ (a :: post)) := by
  induction pre generalizing u with
  | nil =>
    cases u with
    | nil => exact Or.inr ⟨[], rfl, h.symm⟩
    | cons x u =>
      obtain ⟨rfl, htail⟩ := List.cons.inj h
      exact Or.inl ⟨u, rfl, htail⟩
  | cons x pre ih =>
    cases u with
    | nil => exact Or.inr ⟨x::pre, rfl, h.symm⟩
    | cons y u =>
      obtain ⟨rfl, htail⟩ := List.cons.inj h
      rcases ih htail with ⟨r, hr, he⟩ | ⟨l, hl, he⟩
      · exact Or.inl ⟨r, congrArg (List.cons x) hr, he⟩
      · exact Or.inr ⟨l, congrArg (List.cons x) hl, he⟩

private theorem zeros_end (k : ℕ) : zeros k ++ [false] = zeros (k+1) := by
  simp [zeros, List.replicate_succ']

private theorem block_gap {k : ℕ} {pre post : List Bool}
    (h : block k = pre ++ true :: post) :
    post = zeros k ∨ ∃ j < k, ∃ r, post = zeros j ++ true :: r := by
  induction k generalizing pre post with
  | zero =>
    cases pre with
    | nil => simpa [block, zeros] using h.symm
    | cons a pre =>
      have := congrArg List.length h
      simp [block] at this
  | succ k ih =>
    have hs : pre ++ true :: post = block k ++ (block k ++ [false]) := by
      simpa only [block, List.append_assoc] using h.symm
    rcases occurrence_append hs with ⟨r, hr, hp⟩ | ⟨l, hl, ht⟩
    · rcases ih hr with he | ⟨j, hj, r', hj'⟩
      · obtain ⟨tail, ht⟩ := block_first k
        exact Or.inr ⟨k, by omega, tail ++ [false], by simp [hp, he, ht]⟩
      · exact Or.inr ⟨j, by omega, r' ++ block k ++ [false], by
          simp [hp, hj', List.append_assoc]⟩
    · rcases occurrence_append ht.symm with ⟨r, hr, hp⟩ | ⟨l', hl', he⟩
      · rcases ih hr with he | ⟨j, hj, r', hj'⟩
        · exact Or.inl (by rw [hp, he, zeros_end])
        · exact Or.inr ⟨j, by omega, r' ++ [false], by simp [hp, hj', List.append_assoc]⟩
      · cases l' <;> simp at he

private theorem block_tail (k : ℕ) : ∃ pre, block k = pre ++ true :: zeros k := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨pre, hp⟩ := ih
    refine ⟨block k ++ pre, ?_⟩
    conv_lhs =>
      rw [block]
      arg 1
      arg 2
      rw [hp]
    simp only [List.append_assoc, List.cons_append, zeros_end]

private def chunk (k : ℕ) (b : Bool) : List Bool :=
  if b then block k ++ block k ++ [false] else [false]

private def expand (k : ℕ) (l : List Bool) : List Bool := l.flatMap (chunk k)

private theorem chunk_block (k s : ℕ) : expand k (block s) = block (k + 1 + s) := by
  induction s with
  | zero => simp [expand, block, chunk]
  | succ s ih =>
    change expand k (block s ++ block s ++ [false]) =
      block (k+1+s) ++ block (k+1+s) ++ [false]
    simp only [expand, List.flatMap_append] at ih ⊢
    rw [ih]
    rfl

private theorem occurrence_expand (k : ℕ) {l pre post : List Bool}
    (h : pre ++ true :: post = expand k l) :
    ∃ l₁ l₂ u v, l = l₁ ++ true :: l₂ ∧
      chunk k true = u ++ true :: v ∧ pre = expand k l₁ ++ u ∧ post = v ++ expand k l₂ := by
  induction l generalizing pre post with
  | nil => cases pre <;> simp [expand] at h
  | cons b l ih =>
    change pre ++ true :: post = chunk k b ++ expand k l at h
    rcases occurrence_append h with ⟨r, hr, hp⟩ | ⟨p, hp, ht⟩
    · cases b
      · cases pre <;> simp [chunk] at hr
      · exact ⟨[], l, pre, r, rfl, hr, rfl, hp⟩
    · obtain ⟨l₁, l₂, u, v, hl, hc, hp', ht'⟩ := ih ht.symm
      refine ⟨b::l₁, l₂, u, v, congrArg (List.cons b) hl, hc, ?_, ht'⟩
      rw [hp, hp']
      simp [expand, List.append_assoc]

private theorem zeros_len (k : ℕ) : (zeros k).length = k := by simp [zeros]

private theorem zeros_no_true (k : ℕ) : true ∉ zeros k := by simp [zeros]

private theorem zeros_split {j k : ℕ} (h : j ≤ k) : zeros k = zeros j ++ zeros (k-j) := by
  unfold zeros
  rw [← List.replicate_add, Nat.add_sub_of_le h]

private theorem short_gap {r s : List Bool} {j k : ℕ} {b : Bool} (hj : j < k) :
    zeros k ++ b :: s ≠ zeros j ++ true :: r := by
  intro h
  have h1 : zeros (j+1) <+: zeros k ++ b :: s := by
    conv_rhs => rw [zeros_split (show j+1 ≤ k by omega)]
    exact ⟨zeros (k-(j+1)) ++ b::s, by simp [List.append_assoc]⟩
  have h2 : zeros j ++ [true] <+: zeros k ++ b :: s := ⟨r, by simpa [List.append_assoc] using h.symm⟩
  have he := (List.prefix_of_prefix_length_le h2 h1 (by simp [zeros])).eq_of_length (by simp [zeros])
  exact zeros_no_true (j+1) (he ▸ (by simp : true ∈ zeros j ++ [true]))

private theorem parsed_history (k : ℕ) {l pre post : List Bool} {b : Bool}
    (h : pre ++ true :: (zeros k ++ b :: post) = expand k l) :
    ∃ s : List Bool, pre ++ true :: zeros k =
      if b then expand k s ++ block k else expand k s ++ block k ++ block k := by
  obtain ⟨s, t, u, v, _, hc, hp, ht⟩ := occurrence_expand k h
  have hcv : u ++ true :: v = block k ++ (block k ++ [false]) := by
    simpa [chunk, List.append_assoc] using hc.symm
  rcases occurrence_append hcv with ⟨r, hr, hv⟩ | ⟨l', hu, hv⟩
  · have ht' : zeros k ++ b :: post = r ++ (block k ++ [false]) ++ expand k t := by
      rw [ht, hv]
    rcases block_gap hr with he | ⟨j, hj, r', hshort⟩
    · have hb : b = true := by
        obtain ⟨tail, hhead⟩ := block_first k
        rw [he, hhead, List.append_assoc, List.append_assoc] at ht'
        exact (List.cons.inj (List.append_cancel_left ht')).1
      rw [he] at hr
      refine ⟨s, ?_⟩
      rw [hp, hb, hr]
      simp [List.append_assoc]
    · exfalso
      apply short_gap (b := b) hj
      simpa [hshort, List.append_assoc] using ht'
  · rcases occurrence_append hv.symm with ⟨r, hr, ht''⟩ | ⟨x, _, hx⟩
    · have ht' : zeros k ++ b :: post = r ++ [false] ++ expand k t := by rw [ht, ht'']
      rcases block_gap hr with he | ⟨j, hj, r', hshort⟩
      · have hb : b = false := by
          rw [he, List.append_assoc] at ht'
          exact (List.cons.inj (List.append_cancel_left ht')).1
        rw [he] at hr
        refine ⟨s, ?_⟩
        rw [hp, hu, hb, hr]
        simp [List.append_assoc]
      · exfalso
        apply short_gap (b := b) hj
        simpa [hshort, List.append_assoc] using ht'
    · cases x <;> simp at hx

private theorem block_zero_suffix (k : ℕ) : zeros k <:+ block k := by
  obtain ⟨s, h⟩ := block_tail k
  exact ⟨s ++ [true], by simpa [List.append_assoc] using h.symm⟩

private theorem chunk_zero_suffix (k : ℕ) : zeros (k+1) <:+ chunk k true := by
  obtain ⟨p, hp⟩ := block_zero_suffix k
  refine ⟨block k ++ p, ?_⟩
  simpa [← zeros_end, chunk, List.append_assoc] using congrArg (fun x => block k ++ x ++ [false]) hp

private theorem expand_zero_suffix (k : ℕ) (s : List Bool) (j : ℕ)
    (hj : j ≤ k+1) (hlen : j ≤ (expand k s).length) : zeros j <:+ expand k s := by
  induction s using List.reverseRecOn generalizing j with
  | nil => simp [expand] at hlen; subst j; simp [zeros]
  | append_singleton s b ih =>
    have hex : expand k (s ++ [b]) = expand k s ++ chunk k b := by
      simp [expand, List.flatMap_append]
    rw [hex] at hlen ⊢
    cases b with
    | true =>
      have hz : zeros j <:+ zeros (k+1) := by
        refine ⟨zeros (k+1-j), ?_⟩
        unfold zeros
        rw [← replicate_add, show k+1-j+j=k+1 by omega]
      exact hz.trans ((chunk_zero_suffix k).trans (List.suffix_append _ _))
    | false =>
      change j ≤ (expand k s ++ [false]).length at hlen
      change zeros j <:+ expand k s ++ [false]
      cases j with
      | zero => simp [zeros]
      | succ j =>
        have h' : j ≤ (expand k s).length := by simp at hlen; omega
        obtain ⟨p, hp⟩ := ih j (by omega) h'
        exact ⟨p, by rw [← zeros_end, ← List.append_assoc, ← hp]⟩

private def factor (u : List Bool) : Prop := ∃ k, u <:+: block k

private def special (u : List Bool) : Prop := factor (u++[true]) ∧ factor (u++[false])

private theorem factor_extend (u : List Bool) (h : factor u) : ∃ b, factor (u++[b]) := by
  obtain ⟨k, l, r, hr⟩ := h
  cases r with
  | nil =>
    obtain ⟨tail, ht⟩ := block_first k
    refine ⟨true, k+1, l, tail ++ [false], ?_⟩
    simp only [List.append_nil] at hr
    rw [block]
    calc
      _ = (l ++ u) ++ (true :: tail) ++ [false] := by simp [List.append_assoc]
      _ = _ := by rw [hr, ← ht]
  | cons b r =>
    exact ⟨b, k, l, r, by simpa [List.append_assoc] using hr⟩

private theorem special_suffix {u v : List Bool} (h : special v) (hs : u <:+ v) : special u := by
  obtain ⟨l, rfl⟩ := hs
  constructor
  · obtain ⟨k, p, q, he⟩ := h.1
    exact ⟨k, p++l, q, by simpa [List.append_assoc] using he⟩
  · obtain ⟨k, p, q, he⟩ := h.2
    exact ⟨k, p++l, q, by simpa [List.append_assoc] using he⟩

private def common (k : ℕ) := zeros k ++ block k

private theorem common_special (k : ℕ) : special (common k) := by
  obtain ⟨l, ht⟩ := block_zero_suffix k
  obtain ⟨r, hr⟩ := block_first k
  constructor
  · refine ⟨k+2, ?_⟩
    have hblock : block (k+2) = chunk k true ++ chunk k true ++ [false] := by
      simp only [block, chunk, if_true]
    have hzero : zeros k <:+ zeros (k+1) := ⟨[false], by simp [zeros, List.replicate_succ]⟩
    obtain ⟨s, hs⟩ := hzero.trans (chunk_zero_suffix k)
    refine ⟨s, r ++ [false] ++ [false], ?_⟩
    calc
      _ = (s ++ zeros k) ++ (block k ++ (true :: r) ++ [false]) ++ [false] := by
        simp [common, List.append_assoc]
      _ = chunk k true ++ chunk k true ++ [false] := by rw [hs, ← hr]; rfl
      _ = _ := hblock.symm
  · refine ⟨k+1, l, [], ?_⟩
    calc
      _ = (l ++ zeros k) ++ block k ++ [false] := by simp [common, List.append_assoc]
      _ = _ := by rw [ht]; rfl

private theorem marker_history {p : List Bool} {k : ℕ} {b : Bool}
    (h : factor ((p ++ true :: zeros k) ++ [b])) :
    ∃ s, p ++ true :: zeros k <:+
      (if b then expand k s ++ block k else expand k s ++ block k ++ block k) := by
  obtain ⟨m,l,r,hr⟩ := h
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show k+1 ≤ max m (k+1) by omega)
  have hinf : ((p ++ true :: zeros k) ++ [b]) <:+: block (k+1+t) := by
    rw [← ht]
    exact (show ((p ++ true :: zeros k) ++ [b]) <:+: block m from ⟨l,r,hr⟩).trans
      ((block_prefix (show m ≤ max m (k+1) by omega)).isInfix)
  obtain ⟨l',r',h'⟩ := hinf
  have h'' : (l' ++ p) ++ true :: (zeros k ++ b :: r') = expand k (block t) := by
    rw [chunk_block]
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using h'
  obtain ⟨s, hs⟩ := parsed_history k h''
  exact ⟨s, ⟨l', by simpa [List.append_assoc] using hs⟩⟩

/-- The longest common suffix permitting both next letters for a fixed zero-run length. -/
private theorem special_criterion (p : List Bool) (k : ℕ) :
    special (p ++ true :: zeros k) ↔ p ++ true :: zeros k <:+ common k := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := marker_history h.1
    obtain ⟨t, ht⟩ := marker_history h.2
    simp only [if_true, if_false, Bool.false_eq_true] at hs ht
    let u := p ++ true :: zeros k
    have hcomm : common k <:+ expand k t ++ block k ++ block k := by
      obtain ⟨v, hv⟩ := block_zero_suffix k
      refine ⟨expand k t ++ v, ?_⟩
      rw [show expand k t ++ block k ++ block k =
        (expand k t ++ (v ++ zeros k)) ++ block k by rw [← hv]]
      simp [common, List.append_assoc]
    by_cases hlen : u.length ≤ (common k).length
    · exact List.suffix_of_suffix_length_le ht hcomm hlen
    · exfalso
      have htrue : (true :: common k) <:+ expand k t ++ block k ++ block k := by
        obtain ⟨v, hv⟩ := block_tail k
        refine ⟨expand k t ++ v, ?_⟩
        simpa only [common, List.append_assoc, List.cons_append] using
          congrArg (fun x => expand k t ++ x ++ block k) hv.symm
      have hlarge : (true :: common k) <:+ u :=
        List.suffix_of_suffix_length_le htrue ht (by simp; omega)
      have hwrong := hlarge.trans hs
      have hsize : k+1 ≤ (expand k s).length := by
        have hl := hwrong.length_le
        simp [common, zeros] at hl
        omega
      obtain ⟨v, hv⟩ := expand_zero_suffix k s (k+1) (by omega) hsize
      have hfalse : (false :: common k) <:+ expand k s ++ block k := by
        refine ⟨v, ?_⟩
        rw [← hv]
        simp [common, zeros, List.replicate_succ, List.append_assoc]
      have he := (List.suffix_of_suffix_length_le hwrong hfalse (by simp)).eq_of_length (by simp)
      simp at he
  · exact special_suffix (common_special k)

private theorem w_at_block {i k : ℕ} (h : i < (block k).length) : w i = (block k)[i] := by
  have h' : i < (block (i+1)).length := by have := block_long (i+1); omega
  have hw : w i = (block (i+1))[i] := by
    simp [w, iterate_block, List.getD_eq_getElem?_getD, h']
  rcases le_total k (i+1) with hk | hk
  · exact hw.trans ((block_prefix hk).getElem h).symm
  · exact hw.trans ((block_prefix hk).getElem h')

private theorem factor_iff (u : List Bool) :
    factor u ↔ ∃ i : ℕ, ∀ j : Fin u.length, w (i+j) = u[j] := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi, hh⟩ := List.infix_iff_getElem?.mp hk
    refine ⟨i, fun j => ?_⟩
    rw [Nat.add_comm i, w_at_block (show (j:ℕ)+i < (block k).length by omega)]
    exact (List.getElem?_eq_some_iff.mp (hh j j.isLt)).2
  · rintro ⟨i, hi⟩
    let k := i+u.length
    have hk := block_long k
    refine ⟨k, List.infix_iff_getElem?.mpr ⟨i, by omega, fun j hj => ?_⟩⟩
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨by omega, (w_at_block (show j+i < (block k).length by omega)).symm.trans
      (by simpa [Nat.add_comm] using hi ⟨j,hj⟩)⟩

private def language (n : ℕ) : Set (List Bool) := {l | l.length = n ∧ factor l}

private def extensions (n : ℕ) (b : Bool) : Set (List Bool) :=
  {l | l.length = n ∧ factor (l++[b])}

private def specials (n : ℕ) : Set (List Bool) := {l | l.length = n ∧ special l}

private theorem occurrence_count (n : ℕ) :
    OMA.S_oeis_a006697.a n = (language n).ncard := by
  unfold OMA.S_oeis_a006697.a
  refine Set.ncard_congr (fun u _ => List.ofFn u) ?_ ?_ ?_
  · intro u hu
    refine ⟨by simp, (factor_iff _).mpr ?_⟩
    rcases hu with ⟨i, hi⟩
    refine ⟨i, fun j => ?_⟩
    simp only [Fin.getElem_fin, List.getElem_ofFn]
    exact hi ⟨j.val, by simpa using j.isLt⟩
  · intro _ _ _ _ h
    exact List.ofFn_injective h
  · intro u hu
    obtain ⟨hlen, hfactor⟩ := hu
    subst n
    refine ⟨fun i => u[i], (factor_iff _).mp hfactor, List.ofFn_getElem⟩

private theorem finite_words (n : ℕ) : {l : List Bool | l.length = n}.Finite := by
  apply (Set.finite_range (List.ofFn : (Fin n → Bool) → List Bool)).subset
  intro l hl
  change l.length = n at hl
  subst n
  exact ⟨fun i => l[i], List.ofFn_getElem⟩

private theorem factor_prefix {u v : List Bool} (h : factor (u++v)) : factor u :=
  h.imp (fun _ hw => (List.infix_append_left : u <:+: u++v).trans hw)

/-- Every factor has at least one extension, and a special factor contributes one extra extension. -/
private theorem language_difference (n : ℕ) :
    (language (n+1)).ncard = (language n).ncard+(specials n).ncard := by
  have hfinite (b) : (extensions n b).Finite := (finite_words n).subset fun _ h => h.1
  have hleft : language n = extensions n true ∪ extensions n false := by
    ext l
    change (l.length=n ∧ factor l) ↔
      (l.length=n ∧ factor (l++[true])) ∨ (l.length=n ∧ factor (l++[false]))
    constructor
    · rintro ⟨hl, hf⟩
      obtain ⟨b, hb⟩ := factor_extend l hf
      cases b
      · exact Or.inr ⟨hl,hb⟩
      · exact Or.inl ⟨hl,hb⟩
    · rintro (⟨hl,hf⟩ | ⟨hl,hf⟩) <;> exact ⟨hl,factor_prefix hf⟩
  have hright : language (n+1) =
      (fun l => l++[true]) '' extensions n true ∪
      (fun l => l++[false]) '' extensions n false := by
    ext l
    constructor
    · intro hl
      have hlen : l.length=n+1 := hl.1
      have hne : l ≠ [] := by intro he; simp [he] at hlen
      obtain ⟨p,b,rfl⟩ : ∃ p b, p ++ [b] = l :=
        ⟨l.dropLast, l.getLast hne, List.dropLast_append_getLast hne⟩
      have hp : p.length = n := by simpa using hlen
      cases b
      · exact Or.inr ⟨p,⟨hp,hl.2⟩,rfl⟩
      · exact Or.inl ⟨p,⟨hp,hl.2⟩,rfl⟩
    · rintro (⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩) <;> exact ⟨by simp [hp.1],hp.2⟩
  have hinter : extensions n true ∩ extensions n false = specials n := by
    ext l
    change ((l.length=n ∧ factor (l++[true])) ∧
      (l.length=n ∧ factor (l++[false]))) ↔ l.length=n ∧ special l
    unfold special
    tauto
  have hf (b : Bool) : Function.Injective (fun l : List Bool => l++[b]) :=
    fun _ _ he => List.append_cancel_right he
  have hdis : Disjoint ((fun l => l++[true]) '' extensions n true)
      ((fun l => l++[false]) '' extensions n false) := by
    rw [Set.disjoint_left]
    rintro l ⟨p,_,rfl⟩ ⟨q,_,hq⟩
    have he := congrArg List.reverse hq
    simp at he
  rw [hright, Set.ncard_union_eq hdis ((hfinite true).image _) ((hfinite false).image _),
    Set.ncard_image_of_injective _ (hf true), Set.ncard_image_of_injective _ (hf false)]
  have h := Set.ncard_union_add_ncard_inter (extensions n true) (extensions n false) (hfinite true) (hfinite false)
  simpa only [← hleft, hinter] using h.symm

private theorem split_last (l : List Bool) : l = zeros l.length ∨
    ∃ p k, l = p ++ true :: zeros k := by
  induction l using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton l b ih =>
    cases b
    · rcases ih with ih | ⟨p,k,ih⟩
      · exact Or.inl (by rw [List.length_append, List.length_singleton, ← zeros_end, ← ih])
      · exact Or.inr ⟨p,k+1,by rw [ih, List.append_assoc, List.cons_append, zeros_end]⟩
    · exact Or.inr ⟨l,0,rfl⟩

private theorem zeros_count_after (k : ℕ) (r : List Bool) :
    ((zeros k ++ true :: r).takeWhile (!·)).length = k := by
  induction k with
  | zero => simp [zeros]
  | succ k ih => simpa [zeros, List.replicate_succ, List.takeWhile_cons] using congrArg Nat.succ ih

private theorem marker_unique {p q : List Bool} {i j : ℕ}
    (h : p ++ true :: zeros i = q ++ true :: zeros j) : i = j := by
  have hr := congrArg (fun l : List Bool => (l.reverse.takeWhile (!·)).length) h
  simpa only [List.reverse_append, List.reverse_cons, show ∀ k, (zeros k).reverse=zeros k
    from fun k => by simp [zeros], List.append_assoc, List.singleton_append, zeros_count_after] using hr

private def specialIndex (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k => n ≤ (common k).length

private def suffixWord (n k : ℕ) : List Bool :=
  (common k).drop ((common k).length-n)

private theorem suffixWord_length {n k : ℕ} (h : k ∈ specialIndex n) :
    (suffixWord n k).length=n := by
  have hlen := (Finset.mem_filter.mp h).2
  simp [suffixWord]
  omega

private theorem suffixWord_marker {n k : ℕ} (h : k ∈ specialIndex n) :
    ∃ p, suffixWord n k = p ++ true :: zeros k := by
  obtain ⟨p,hp⟩ := block_tail k
  have hs : true :: zeros k <:+ common k := ⟨zeros k ++ p,by
    simp only [common, hp, List.append_assoc]⟩
  have hi := Finset.mem_range.mp (Finset.mem_filter.mp h).1
  have hlen : (true :: zeros k).length ≤ (suffixWord n k).length := by
    rw [suffixWord_length h]
    simp [zeros]
    omega
  obtain ⟨p', hp'⟩ := List.suffix_of_suffix_length_le hs
    (show suffixWord n k <:+ common k from List.drop_suffix _ _) hlen
  exact ⟨p', hp'.symm⟩

private theorem specials_count (n : ℕ) : (specials n).ncard = 1 + (specialIndex n).card := by
  classical
  let s : Set (List Bool) := {zeros n}
  let t : Set (List Bool) := suffixWord n '' (↑(specialIndex n) : Set ℕ)
  have hst : specials n = s ∪ t := by
    ext u
    constructor
    · intro hu
      have hlen : u.length = n := hu.1
      rcases split_last u with hu' | ⟨p,k,hu'⟩
      · exact Or.inl (by simpa only [s, Set.mem_singleton_iff, hlen] using hu')
      · have hs : u <:+ common k := by
          rw [hu']
          exact (special_criterion p k).mp (hu' ▸ hu.2)
        have hk : k ∈ specialIndex n := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlen ▸ hs.length_le⟩
          have h := congrArg List.length hu'
          simp [hlen, zeros] at h
          omega
        have hsu := List.suffix_of_suffix_length_le hs
          (show suffixWord n k <:+ common k from List.drop_suffix _ _)
          (by rw [suffixWord_length hk, hlen])
        exact Or.inr ⟨k,hk,(hsu.eq_of_length (by rw [hlen,suffixWord_length hk])).symm⟩
    · rintro (hs | ⟨k,hk,rfl⟩)
      · change u = zeros n at hs
        subst u
        exact ⟨zeros_len n,special_suffix (common_special n)
          ((block_zero_suffix n).trans (List.suffix_append _ _))⟩
      · exact ⟨suffixWord_length hk, special_suffix (common_special k) (List.drop_suffix _ _)⟩
  have hdis : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro u hu ⟨k,hk,rfl⟩
    change suffixWord n k = zeros n at hu
    obtain ⟨p,hp⟩ := suffixWord_marker hk
    exact zeros_no_true n (hu ▸ (hp.symm ▸ (by simp : true ∈ p ++ true :: zeros k)))
  have hcount : t.ncard = (specialIndex n).card := by
    change (suffixWord n '' (↑(specialIndex n) : Set ℕ)).ncard = _
    rw [Set.InjOn.ncard_image]
    · exact Set.ncard_coe_finset _
    · intro i hi j hj hij
      obtain ⟨p,hp⟩ := suffixWord_marker hi
      obtain ⟨q,hq⟩ := suffixWord_marker hj
      exact marker_unique (hp.symm.trans (hij.trans hq))
  rw [hst, Set.ncard_union_eq hdis (Set.finite_singleton _) ((specialIndex n).finite_toSet.image _),
    hcount]
  simp [s]

private def formula (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n+1), min (2^i) (n-i+1)

private theorem formula_difference (n : ℕ) : formula (n+1) = formula n + 1 + (specialIndex n).card := by
  unfold formula
  rw [Finset.sum_range_succ (fun i => min (2^i) (n+1-i+1)) (n+1)]
  have hp : (0:ℕ) < 2^(n+1) := by positivity
  simp only [Nat.sub_self, Nat.zero_add, Nat.min_eq_right (show 1 ≤ (2:ℕ)^(n+1) by omega)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hsum (k : ℕ) (hk : k ∈ Finset.range n) :
      min (2 ^ (k+1)) (n+1-(k+1)+1) =
        min (2^(k+1)) (n-(k+1)+1) + if n ≤ (common k).length then 1 else 0 := by
    have hk' := Finset.mem_range.mp hk
    have h := block_length k
    simp only [common, List.length_append, zeros_len]
    split_ifs with h' <;> omega
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
  have hc : (∑ k ∈ Finset.range n, if n ≤ (common k).length then 1 else 0) =
      (specialIndex n).card := by
    simp [specialIndex]
  rw [hc]
  simp
  have hp : (0:ℕ) < 2^n := by positivity
  omega

private theorem complexity (n : ℕ) : OMA.S_oeis_a006697.a n = formula n := by
  induction n with
  | zero =>
    have h : language 0 = {[]} := by
      ext l
      cases l <;> simp [language, factor]
    rw [occurrence_count, h]
    simp [formula]
  | succ n ih =>
    rw [occurrence_count, language_difference, specials_count, ← occurrence_count,
      ih, formula_difference]
    omega

private theorem triangular_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (k+1)) = (n+1).choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := Nat.choose_succ_succ (n+1) 1
    change (n+2).choose 2 = (n+1).choose 1 + (n+1).choose 2 at h
    rw [Nat.choose_one_right] at h
    rw [Finset.sum_range_succ, ih, h, Nat.add_comm]

private theorem coefficient_identity (m : ℕ) :
    (formula (m+1) : ℤ) =
      1 + ((m+2).choose 2 : ℤ) -
        ∑ k ∈ (Finset.Icc 1 m).filter (fun k => 2^k+k-1 ≤ m),
          ((m : ℤ) - (2^k+k-1) + 1) := by
  unfold formula
  rw [Finset.sum_range_succ', Nat.cast_add, Nat.cast_sum]
  simp only [pow_zero, Nat.sub_zero, Nat.min_eq_left (by omega : 1 ≤ m+1+1), Nat.cast_one]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (m+1)) :
      (min (2^(k+1)) (m+1-(k+1)+1) : ℕ) =
        (m+1-k) - (if 2^(k+1)+(k+1)-1 ≤ m then m+1-k-2^(k+1) else 0) := by
    have hk' := Finset.mem_range.mp hk
    have hp : 0 < 2 ^ (k+1) := by positivity
    split_ifs <;> omega
  have hsum :
      (∑ k ∈ Finset.range (m+1), (m+1-k)) = (m+2).choose 2 := by
    calc
      _ = ∑ k ∈ Finset.range (m+1), ((m+1-1-k)+1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        omega
      _ = ∑ k ∈ Finset.range (m+1), (k+1) := Finset.sum_range_reflect (fun k => k+1) (m+1)
      _ = _ := triangular_sum (m+1)
  have hdiff :
      (∑ k ∈ Finset.range (m+1),
        ((min (2^(k+1)) (m+1-(k+1)+1) : ℕ) : ℤ)) =
      (m+2).choose 2 - (∑ k ∈ Finset.range (m+1),
        if 2^(k+1)+(k+1)-1 ≤ m then
          (m : ℤ) - (2 ^ (k+1) + (k+1) - 1) + 1 else 0) := by
    rw [← hsum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hterm k hk]
    split_ifs with he
    · have hp : (0:ℕ) < 2^(k+1) := by positivity
      have heq : ((m+1-k-2^(k+1) : ℕ) : ℤ) =
          (m : ℤ) - (2^(k+1)+(k+1)-1) + 1 := by
        have hk1 : k ≤ m+1 := by omega
        have hk2 : (2:ℕ)^(k+1) ≤ m+1-k := by omega
        rw [Nat.cast_sub hk2, Nat.cast_sub hk1]
        push_cast
        ring
      rw [← heq, Nat.cast_sub (by omega)]
    · simp
  rw [hdiff]
  have hreindex :
      (∑ k ∈ Finset.range (m+1), if 2^(k+1)+(k+1)-1 ≤ m then
        (m : ℤ) - (2 ^ (k+1) + (k+1) - 1) + 1 else 0) =
      ∑ k ∈ (Finset.Icc 1 m).filter (fun k => 2^k+k-1 ≤ m),
        ((m : ℤ) - (2^k+k-1) + 1) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun k _ => k+1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hk ⊢
      have h := hk.2
      have hpow : 0 < 2^(k+1) := by positivity
      omega
    · intro a ha b hb he
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hk ⊢
      exact ⟨k-1,⟨by omega,by simpa [show k-1+1=k by omega] using hk.2⟩,by omega⟩
    · simp
  rw [hreindex]
  ring

end OMA.A006697

theorem OMA.solution : type_of% @OMA.S_oeis_a006697.main := by
  intro m _
  rw [OMA.A006697.complexity, OMA.A006697.coefficient_identity]
