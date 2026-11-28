import FormalConjectures.ErdosProblems.«111»

-- Problem: Erdős Problem 111 — erdos conjecture
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/111.lean:129 (declaration Erdos111.erdos_111.variants.erdos_conjecture)
-- Credit: @chris01-dev
--
-- For every k >= 2 the graph is a labelled shift graph on k-tuples. Its vertices are lists
-- (x_1, ..., x_k) over the (k-1)-fold iterated power set of a domain D that is a disjoint
-- union of blocks of size beth_i, i < omega_1. Two tuples can only be adjacent when one is
-- the shift of the other: (x_1, ..., x_k) and (x_2, ..., x_(k+1)).
--
-- Finite bound (colour_exists, deletion_bound). For a set S of n tuples and a threshold s,
-- let B_k = S and let B_(j-1) be the (j-1)-tuples with at least s left extensions in B_j, so
-- that |B_(j-1)| <= |B_j| / s. Colour a j-tuple u of B_j by the colour of its first j-1
-- entries when these lie in B_(j-1), by the opposite of the colour of its last j-1 entries
-- when only these lie in B_(j-1), and by 0 otherwise. Then every tuple v has at most
-- max(s, n / s^(k-1)) predecessors of its own colour. With s the ceiling of n^(1/k) this
-- gives h(n) <= n * s, which is O(n^(1+1/k)).
--
-- Chromatic number. A point of difference of two distinct sets is chosen (pcs), and dl maps
-- a list to the list of chosen difference points of consecutive entries, one level down.
-- Iterating dl on a k-tuple ends in one point of D, and the label of the tuple is the level
-- (block index) of that point. Shifts with different labels are adjacent, so the label is a
-- proper colouring with aleph_1 colours. A colouring by the naturals is refuted in two steps:
-- the argument of the merged proof of the n^(3/2) variant (colour patterns, a countable
-- supremum of labels, restriction below that level) yields a proper colouring of the shift
-- digraph on (k-1)-tuples with at most |D| colours, and then the classical colour-pattern
-- argument (lemma chain) descends to an injection of the iterated power set into a set of
-- smaller cardinality. Degenerate tuples are handled by one extra bit per colour (bit).
--
-- The definitions of Level, Block, Domain and the lemmas up to prefix_sets_le, and the shape
-- of the proofs of not_colorable_nat, chromatic_graph and of the final counting in
-- deletion_bound, are taken from the merged proof of
-- Erdos111.erdos_111.variants.upper_bound_existence in this repository.

namespace OMA.E111c

open Cardinal Ordinal Set Filter SimpleGraph
open scoped Cardinal Ordinal

abbrev Level := (ω₁ : Ordinal.{0}).ToType
noncomputable def firstLevel : Level := Ordinal.ToType.mk ⟨0,Ordinal.omega_pos _⟩
noncomputable def nextLevel (i : Level) : Level :=
  Ordinal.ToType.mk ⟨Order.succ i.toOrd.val,by
    change Order.succ i.toOrd.val < (ω₁ : Ordinal.{0})
    exact (Cardinal.isSuccLimit_omega 1).succ_lt
      (show i.toOrd.val < (ω₁ : Ordinal.{0}) from i.toOrd.property)⟩

lemma next_index (i : Level) : (nextLevel i).toOrd.val = Order.succ i.toOrd.val := by
  simp [nextLevel, Ordinal.ToType.toOrd]

lemma bounded_levels (f : ℕ → Level) : ∃ b : Level, ∀ n, f n ≤ b := by
  let b : Set.Iio (ω₁ : Ordinal.{0}) := ⟨⨆ n, (f n).toOrd.val,
    Ordinal.iSup_lt_omega_one (fun n => (f n).toOrd.property)⟩
  refine ⟨Ordinal.ToType.mk b,fun n => ?_⟩
  apply Ordinal.ToType.mk.symm.le_iff_le.mp
  rw [OrderIso.symm_apply_apply]
  change (f n).toOrd.val ≤ ⨆ i, (f i).toOrd.val
  exact le_ciSup Ordinal.bddAbove_of_small n

def Block (i : Level) := (ℶ_ i.toOrd.val).out
abbrev Domain := (i : Level) × Block i
abbrev Prefix (i : Level) := {d : Domain // d.1 ≤ i}

lemma block_size (i : Level) : #(Block i) = ℶ_ i.toOrd.val := Cardinal.mk_out _
lemma level_size : #Level = ℵ₁ := by rw [Cardinal.mk_toType,Ordinal.card_omega]

lemma block_le_domain (i : Level) : ℶ_ i.toOrd.val ≤ #Domain := by
  rw [← block_size]
  exact Cardinal.mk_le_of_injective (sigma_mk_injective (i := i))

lemma omega_one_le_next (i : Level) : ℵ₁ ≤ ℶ_ (nextLevel i).toOrd.val := by
  rw [next_index]
  apply (Cardinal.aleph_le_beth 1).trans (Cardinal.beth_le_beth.mpr ?_)
  simp

lemma prefix_size (i : Level) : #(Prefix i) ≤ ℶ_ (nextLevel i).toOrd.val := by
  classical
  have hle {j : Level} (hj : j ≤ i) : #(Block j) ≤ #(Block i) := by
    rw [block_size,block_size]
    exact Cardinal.beth_le_beth.mpr (Ordinal.ToType.mk.symm.monotone hj)
  let emb {j : Level} (hj : j ≤ i) : Block j ↪ Block i := Classical.choice ((Cardinal.le_def _ _).mp (hle hj))
  let f (x : Prefix i) : Level × Block i := (x.val.1,emb x.property x.val.2)
  have inj : Function.Injective f := by
    rintro ⟨⟨j,x⟩,hx⟩ ⟨⟨k,y⟩,hy⟩ eq
    obtain rfl : j = k := congrArg Prod.fst eq
    have eq' : x = y := (emb hx).injective (congrArg Prod.snd eq)
    subst y
    rfl
  apply (Cardinal.mk_le_of_injective inj).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_id, level_size, block_size]
  apply (mul_le_mul' (omega_one_le_next i)
    (Cardinal.beth_le_beth.mpr (show i.toOrd.val ≤ (nextLevel i).toOrd.val by rw [next_index]; exact Order.le_succ _))).trans
  exact (Cardinal.mul_eq_self (Cardinal.aleph0_le_beth _)).le

lemma prefix_sets_le (i : Level) : #(Set (Prefix i)) ≤ #Domain := by
  rw [Cardinal.mk_set]
  calc (2 : Cardinal) ^ #(Prefix i) ≤ 2 ^ ℶ_ (nextLevel i).toOrd.val :=
        Cardinal.power_le_power_left two_ne_zero (prefix_size i)
       _ = ℶ_ (nextLevel (nextLevel i)).toOrd.val := by rw [next_index (nextLevel i),Cardinal.beth_succ]
       _ ≤ _ := block_le_domain _

lemma block_nonempty (i : Level) : Nonempty (Block i) := by
  rw [← Cardinal.mk_ne_zero_iff, block_size]
  exact (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_beth _)).ne'

lemma aleph0_le_domain : ℵ₀ ≤ #Domain :=
  aleph0_lt_aleph_one.le.trans ((omega_one_le_next firstLevel).trans (block_le_domain _))

noncomputable def dom0 : Domain := ⟨firstLevel, Classical.choice (block_nonempty firstLevel)⟩

section generic
variable {Y : Type}

noncomputable def pcs (d : Y) (x y : Set Y) : Y := by
  classical
  exact if h : ∃ a, ¬ (a ∈ x ↔ a ∈ y) then Classical.choose h else d

lemma pcs_spec (d : Y) {x y : Set Y} (h : x ≠ y) : ¬ (pcs d x y ∈ x ↔ pcs d x y ∈ y) := by
  classical
  have h' : ∃ a, ¬ (a ∈ x ↔ a ∈ y) := by
    by_contra hc
    exact h (Set.ext fun a => not_not.mp (not_exists.mp hc a))
  unfold pcs
  rw [dif_pos h']
  exact Classical.choose_spec h'

noncomputable def dl (d : Y) : List (Set Y) → List Y
  | x :: y :: r => pcs d x y :: dl d (y :: r)
  | [_] => []
  | [] => []

lemma dl_cons_cons (d : Y) (x y : Set Y) (r : List (Set Y)) :
    dl d (x :: y :: r) = pcs d x y :: dl d (y :: r) := by
  rw [dl]

lemma dl_single (d : Y) (x : Set Y) : dl d [x] = [] := by
  rw [dl]

lemma dl_nil (d : Y) : dl d ([] : List (Set Y)) = [] := by
  rw [dl]

lemma dl_tail (d : Y) (l : List (Set Y)) : dl d l.tail = (dl d l).tail := by
  match l with
  | [] => simp [dl_nil]
  | [x] => simp [dl_nil, dl_single]
  | x :: y :: r => simp [dl_cons_cons]

lemma dl_dropLast (d : Y) : ∀ l : List (Set Y), dl d l.dropLast = (dl d l).dropLast
  | [] => by simp [dl_nil]
  | [x] => by simp [dl_nil, dl_single]
  | [x, y] => by simp [dl_cons_cons, dl_single]
  | x :: y :: z :: r => by
      have ih := dl_dropLast d (y :: z :: r)
      rw [List.dropLast_cons_cons, dl_cons_cons] at ih
      rw [List.dropLast_cons_cons, List.dropLast_cons_cons, dl_cons_cons, dl_cons_cons,
        dl_cons_cons, List.dropLast_cons_cons, ← ih]

lemma dl_length (d : Y) : ∀ l : List (Set Y), (dl d l).length = l.length - 1
  | [] => by simp [dl_nil]
  | [x] => by simp [dl_single]
  | x :: y :: r => by
      have ih := dl_length d (y :: r)
      rw [dl_cons_cons, List.length_cons, ih]
      simp

def nd : List (Set Y) → Prop
  | x :: y :: r => x ≠ y ∧ nd (y :: r)
  | [_] => True
  | [] => True

lemma nd_cons_cons (x y : Set Y) (r : List (Set Y)) :
    nd (x :: y :: r) ↔ (x ≠ y ∧ nd (y :: r)) := by
  rw [nd]

lemma nd_single (x : Set Y) : nd [x] := by
  rw [nd]; trivial

lemma nd_nil : nd ([] : List (Set Y)) := by
  rw [nd]; trivial

lemma nd_of_parts (x y z : Set Y) (r : List (Set Y))
    (hd : nd (x :: y :: z :: r).dropLast) (ht : nd (x :: y :: z :: r).tail) :
    nd (x :: y :: z :: r) := by
  rw [List.dropLast_cons_cons, List.dropLast_cons_cons, nd_cons_cons] at hd
  rw [nd_cons_cons]
  exact ⟨hd.1, ht⟩

end generic

structure Lvl where
  Z : Type
  d : Z
  rank : ℕ
  Good : List Z → Prop
  lab : List Z → Level
  bit : List Z → Prop
  up : List (Set Z) → Set Domain

noncomputable def base : Lvl where
  Z := Domain
  d := dom0
  rank := 0
  Good := fun _ => True
  lab := fun l => (l.headD dom0).1
  bit := fun _ => False
  up := fun l => l.headD ∅

def nGood (L : Lvl) (l : List (Set L.Z)) : Prop := nd l ∧ L.Good (dl L.d l)

noncomputable def nlab (L : Lvl) (l : List (Set L.Z)) : Level := L.lab (dl L.d l)

noncomputable def nbit (L : Lvl) (l : List (Set L.Z)) : Prop :=
  if l.length = 2 then pcs L.d (l.headD ∅) (l.tail.headD ∅) ∈ l.headD ∅ else L.bit (dl L.d l)

noncomputable def nup (L : Lvl) (l : List (Set (Set L.Z))) : Set Domain :=
  L.up (dl (∅ : Set L.Z) l)

noncomputable def next (L : Lvl) : Lvl where
  Z := Set L.Z
  d := ∅
  rank := L.rank + 1
  Good := nGood L
  lab := nlab L
  bit := nbit L
  up := nup L

structure Ok (L : Lvl) : Prop where
  good_nil : L.Good []
  good_single : ∀ x, L.Good [x]
  bit_parts : ∀ v : List L.Z, 3 ≤ v.length → L.Good v.dropLast → L.Good v.tail →
    ¬ L.Good v → ¬ (L.bit v.dropLast ↔ L.bit v.tail)
  pair : (∀ x y, L.Good [x, y] ↔ x ≠ y) ∨ (∀ l, L.Good l)
  lab_gt : ∀ (v : List (Set L.Z)) (i : Level), L.rank + 2 ≤ v.length →
    (nd v ∧ L.Good (dl L.d v)) →
    (∀ d : Domain, d.1 ≤ i → (d ∈ L.up v.dropLast ↔ d ∈ L.up v.tail)) →
    i < L.lab (dl L.d v)
  card : #L.Z = (fun c : Cardinal.{0} => 2 ^ c)^[L.rank] #Domain

lemma nGood_iff (L : Lvl) (l : List (Set L.Z)) :
    nGood L l ↔ (nd l ∧ L.Good (dl L.d l)) := Iff.rfl

lemma nGood_pair (L : Lvl) (h : Ok L) (x y : Set L.Z) : nGood L [x, y] ↔ x ≠ y := by
  rw [nGood_iff, dl_cons_cons, dl_single, nd_cons_cons]
  exact ⟨fun hh => hh.1.1, fun hh => ⟨⟨hh, nd_single _⟩, h.good_single _⟩⟩

lemma nbit_two (L : Lvl) (x y : Set L.Z) : nbit L [x, y] ↔ pcs L.d x y ∈ x := by
  unfold nbit
  simp

lemma nbit_of_ne (L : Lvl) (l : List (Set L.Z)) (h : l.length ≠ 2) :
    nbit L l = L.bit (dl L.d l) := by
  unfold nbit
  rw [if_neg h]

lemma nbit_parts (L : Lvl) (h : Ok L) : ∀ v : List (Set L.Z), 3 ≤ v.length →
    nGood L v.dropLast → nGood L v.tail → ¬ nGood L v →
    ¬ (nbit L v.dropLast ↔ nbit L v.tail)
  | [], h3, _, _, _ => by simp at h3
  | [_], h3, _, _, _ => by simp at h3
  | [_, _], h3, _, _, _ => by simp at h3
  | [x1, x2, x3], _, hd, ht, hn => by
      rw [nGood_iff] at hd ht hn
      have hnd : nd [x1, x2, x3] := nd_of_parts x1 x2 x3 [] hd.1 ht.1
      have hne : x1 ≠ x2 := ((nd_cons_cons _ _ _).mp hnd).1
      have hng : ¬ L.Good (dl L.d [x1, x2, x3]) := fun hh => hn ⟨hnd, hh⟩
      rw [dl_cons_cons, dl_cons_cons, dl_single] at hng
      have heq : pcs L.d x1 x2 = pcs L.d x2 x3 := by
        rcases h.pair with hp | hp
        · by_contra hne2
          exact hng ((hp _ _).mpr hne2)
        · exact absurd (hp _) hng
      show ¬ (nbit L [x1, x2] ↔ nbit L [x2, x3])
      rw [nbit_two, nbit_two, ← heq]
      exact pcs_spec L.d hne
  | x1 :: x2 :: x3 :: x4 :: r, _, hd, ht, hn => by
      rw [nGood_iff] at hd ht hn
      have hnd : nd (x1 :: x2 :: x3 :: x4 :: r) :=
        nd_of_parts x1 x2 x3 (x4 :: r) hd.1 ht.1
      have hng : ¬ L.Good (dl L.d (x1 :: x2 :: x3 :: x4 :: r)) := fun hh => hn ⟨hnd, hh⟩
      have h1 := hd.2
      have h2 := ht.2
      rw [dl_dropLast] at h1
      rw [dl_tail] at h2
      have hlen : 3 ≤ (dl L.d (x1 :: x2 :: x3 :: x4 :: r)).length := by
        rw [dl_length]; simp
      have key := h.bit_parts _ hlen h1 h2 hng
      rw [nbit_of_ne L _ (by simp), nbit_of_ne L _ (by simp), dl_dropLast, dl_tail]
      exact key

lemma nGood_nil (L : Lvl) (h : Ok L) : nGood L [] := by
  rw [nGood_iff, dl_nil]
  exact ⟨nd_nil, h.good_nil⟩

lemma nGood_single (L : Lvl) (h : Ok L) (x : Set L.Z) : nGood L [x] := by
  rw [nGood_iff, dl_single]
  exact ⟨nd_single x, h.good_nil⟩

lemma nlab_gt (L : Lvl) (h : Ok L) (v : List (Set (Set L.Z))) (i : Level)
    (hlen : L.rank + 1 + 2 ≤ v.length)
    (hg : nd v ∧ nGood L (dl (∅ : Set L.Z) v))
    (hagree : ∀ d : Domain, d.1 ≤ i → (d ∈ nup L v.dropLast ↔ d ∈ nup L v.tail)) :
    i < nlab L (dl (∅ : Set L.Z) v) := by
  have hlen2 : L.rank + 2 ≤ (dl (∅ : Set L.Z) v).length := by
    rw [dl_length]
    omega
  refine h.lab_gt (dl (∅ : Set L.Z) v) i hlen2 hg.2 ?_
  intro d hd
  have h1 := hagree d hd
  unfold nup at h1
  rw [dl_dropLast, dl_tail] at h1
  exact h1

lemma ncard (L : Lvl) (h : Ok L) :
    #(Set L.Z) = (fun c : Cardinal.{0} => 2 ^ c)^[L.rank + 1] #Domain := by
  rw [Function.iterate_succ_apply', ← h.card, Cardinal.mk_set]

lemma base_lab_gt (v : List (Set Domain)) (i : Level) (hlen : 2 ≤ v.length)
    (hg : nd v)
    (h : ∀ d : Domain, d.1 ≤ i → (d ∈ v.dropLast.headD ∅ ↔ d ∈ v.tail.headD ∅)) :
    i < ((dl dom0 v).headD dom0).1 := by
  match v, hlen, hg, h with
  | [], hlen, _, _ => simp at hlen
  | [_], hlen, _, _ => simp at hlen
  | x :: y :: r, _, hg, h =>
    have hne : x ≠ y := ((nd_cons_cons _ _ _).mp hg).1
    by_contra hlt
    rw [not_lt, dl_cons_cons, List.headD_cons] at hlt
    have h1 := h (pcs dom0 x y) hlt
    rw [List.dropLast_cons_cons, List.headD_cons, List.tail_cons, List.headD_cons] at h1
    exact pcs_spec dom0 hne h1

lemma base_ok : Ok base where
  good_nil := trivial
  good_single := fun _ => trivial
  bit_parts := fun _ _ _ _ hn => absurd trivial hn
  pair := Or.inr fun _ => trivial
  lab_gt := fun v i hlen hg h => base_lab_gt v i hlen hg.1 h
  card := rfl

lemma next_ok (L : Lvl) (h : Ok L) : Ok (next L) where
  good_nil := nGood_nil L h
  good_single := nGood_single L h
  bit_parts := nbit_parts L h
  pair := Or.inl (nGood_pair L h)
  lab_gt := nlab_gt L h
  card := ncard L h

noncomputable def tower : ℕ → Lvl
  | 0 => base
  | (j + 1) => next (tower j)

lemma tower_ok : ∀ j : ℕ, Ok (tower j)
  | 0 => base_ok
  | (j + 1) => next_ok (tower j) (tower_ok j)

lemma tower_rank : ∀ j : ℕ, (tower j).rank = j
  | 0 => rfl
  | (j + 1) => by
      show (tower j).rank + 1 = j + 1
      rw [tower_rank j]

lemma chain {Z : Type} (Gd : List Z → Prop) (bt : List Z → Prop)
    (hpair : ∀ x y : Z, Gd [x, y] ↔ x ≠ y)
    (hbit : ∀ v : List Z, 3 ≤ v.length → Gd v.dropLast → Gd v.tail →
      ¬ Gd v → ¬ (bt v.dropLast ↔ bt v.tail)) :
    ∀ (n : ℕ) (κ : Cardinal.{0}), ℵ₀ ≤ κ → (fun c : Cardinal.{0} => 2 ^ c)^[n] κ < #Z →
    ∀ (C : Type) (e : List Z → C), #C ≤ κ →
    (∀ v : List Z, v.length = n + 2 → Gd v → e v.dropLast ≠ e v.tail) →
    False := by
  intro n
  induction n with
  | zero =>
    intro κ _ hκ C e hC hprop
    have inj : Function.Injective (fun x : Z => e [x]) := by
      intro x y hxy
      by_contra hne
      exact hprop [x, y] rfl ((hpair x y).mpr hne) hxy
    have h1 : #Z ≤ #C := Cardinal.mk_le_of_injective inj
    exact hκ.not_ge (h1.trans hC)
  | succ n ih =>
    intro κ hinf hκ C e hC hprop
    let ρ : List Z → Set (C × Prop) := fun q =>
      {cb | ∃ y : Z, Gd (q ++ [y]) ∧ (e (q ++ [y]), bt (q ++ [y])) = cb}
    refine ih (2 ^ κ) (hinf.trans (Cardinal.cantor κ).le) ?_ (Set (C × Prop)) ρ ?_ ?_
    · rw [Function.iterate_succ_apply] at hκ
      exact hκ
    · rw [Cardinal.mk_set]
      refine Cardinal.power_le_power_left two_ne_zero ?_
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_Prop]
      calc #C * 2 ≤ κ * κ := by
            gcongr
            exact (Cardinal.natCast_lt_aleph0 (n := 2)).le.trans hinf
        _ = κ := Cardinal.mul_eq_self hinf
    · intro v hlen hgood heq
      have hne : v ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen
      have hv : v.dropLast ++ [v.getLast hne] = v := List.dropLast_append_getLast hne
      have hmem : (e v, bt v) ∈ ρ v.dropLast :=
        ⟨v.getLast hne, by rw [hv]; exact hgood, by rw [hv]⟩
      rw [heq] at hmem
      obtain ⟨y, hy, hyeq⟩ := hmem
      have he : e (v.tail ++ [y]) = e v := congrArg Prod.fst hyeq
      have hb : bt (v.tail ++ [y]) = bt v := congrArg Prod.snd hyeq
      have hd : (v ++ [y]).dropLast = v := List.dropLast_concat
      have ht : (v ++ [y]).tail = v.tail ++ [y] := List.tail_append_of_ne_nil hne
      have hl : (v ++ [y]).length = n + 1 + 2 := by simp [hlen]
      by_cases hw : Gd (v ++ [y])
      · have := hprop (v ++ [y]) hl hw
        rw [hd, ht] at this
        exact this he.symm
      · have := hbit (v ++ [y]) (by omega) (by rw [hd]; exact hgood)
          (by rw [ht]; exact hy) hw
        rw [hd, ht, hb] at this
        exact this Iff.rfl

abbrev W (L : Lvl) := {l : List (Set L.Z) // l.length = L.rank + 2 ∧ nGood L l}

noncomputable def graph (L : Lvl) : SimpleGraph (W L) where
  Adj u v := (u.val.tail = v.val.dropLast ∨ v.val.tail = u.val.dropLast) ∧
    nlab L u.val ≠ nlab L v.val
  symm := ⟨fun _ _ h => ⟨h.1.elim (fun h => Or.inr h) (fun h => Or.inl h), h.2.symm⟩⟩
  loopless := ⟨by intro e h; exact h.2 rfl⟩

lemma not_colorable_nat (L : Lvl) (hL : Ok L)
    (c : (graph L).Coloring ℕ) : False := by
  classical
  let c' : List (Set L.Z) → ℕ := fun l =>
    if h : l.length = L.rank + 2 ∧ nGood L l then c ⟨l, h⟩ else 0
  let pattern (p : List (Set L.Z)) : Set ℕ :=
    {m | ∃ x : Set L.Z, (x :: p).length = L.rank + 2 ∧ nGood L (x :: p) ∧ c' (x :: p) = m}
  let chosen (p : List (Set L.Z)) (m : ℕ) : Level :=
    if h : m ∈ pattern p then nlab L (Classical.choose h :: p) else firstLevel
  choose cut hcut using fun p => bounded_levels (chosen p)
  let enc (i : Level) : Set (Prefix i) ↪ Domain :=
    Classical.choice ((Cardinal.le_def _ _).mp (prefix_sets_le i))
  let e (p : List (Set L.Z)) : Set ℕ × Level × Domain :=
    (pattern p, cut p, enc (cut p) (Subtype.val ⁻¹' L.up p))
  refine chain (nGood L) (nbit L) (nGood_pair L hL) (nbit_parts L hL) L.rank #Domain
    aleph0_le_domain ?_ _ e ?_ ?_
  · rw [Cardinal.mk_set, ← hL.card]
    exact Cardinal.cantor _
  · have hD : ℵ₁ ≤ #Domain := (omega_one_le_next firstLevel).trans (block_le_domain _)
    have hN : #(Set ℕ) ≤ #Domain := by
      rw [Cardinal.mk_set, Cardinal.mk_nat]
      change 𝔠 ≤ #Domain
      rw [← Cardinal.beth_one]
      apply (Cardinal.beth_le_beth.mpr (show 1 ≤ (nextLevel firstLevel).toOrd.val by
        rw [next_index]; simp)).trans (block_le_domain _)
    have hinfinite : ℵ₀ ≤ #Domain := aleph0_le_domain
    simp only [Cardinal.mk_prod, Cardinal.lift_id, level_size]
    calc #(Set ℕ) * (ℵ₁ * #Domain) ≤ #Domain * (#Domain * #Domain) := by gcongr
      _ = #Domain := by rw [Cardinal.mul_eq_self hinfinite, Cardinal.mul_eq_self hinfinite]
  · intro v hlen hgood heq
    have hne : v ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    have hp : pattern v.dropLast = pattern v.tail := congrArg Prod.fst heq
    have hc : cut v.dropLast = cut v.tail := congrArg (Prod.fst ∘ Prod.snd) heq
    have codes : enc (cut v.dropLast) (Subtype.val ⁻¹' L.up v.dropLast) =
        enc (cut v.tail) (Subtype.val ⁻¹' L.up v.tail) :=
      congrArg (Prod.snd ∘ Prod.snd) heq
    rw [← hc] at codes
    have hs := (enc (cut v.dropLast)).injective codes
    obtain ⟨x1, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hmem : c' (x1 :: t) ∈ pattern (x1 :: t).tail := ⟨x1, hlen, hgood, rfl⟩
    rw [← hp] at hmem
    have hx0 := Classical.choose_spec hmem
    let u : W L :=
      ⟨Classical.choose hmem :: (x1 :: t).dropLast, hx0.1, hx0.2.1⟩
    let vv : W L := ⟨x1 :: t, hlen, hgood⟩
    have cu : c u = c vv := by
      have h1 : c' (Classical.choose hmem :: (x1 :: t).dropLast) = c u :=
        dif_pos ⟨hx0.1, hx0.2.1⟩
      have h2 : c' (x1 :: t) = c vv := dif_pos ⟨hlen, hgood⟩
      rw [← h1, ← h2]
      exact hx0.2.2
    have hlabel : nlab L (Classical.choose hmem :: (x1 :: t).dropLast) =
        nlab L (x1 :: t) := by
      by_contra h
      exact c.valid (show (graph L).Adj u vv from ⟨Or.inl rfl, h⟩) cu
    have hl := hcut (x1 :: t).dropLast (c' (x1 :: t))
    rw [show chosen (x1 :: t).dropLast (c' (x1 :: t)) =
      nlab L (Classical.choose hmem :: (x1 :: t).dropLast) from dif_pos hmem, hlabel] at hl
    have hgt := hL.lab_gt (x1 :: t) (cut (x1 :: t).dropLast) (le_of_eq hlen.symm) hgood
      (fun d hd => Set.ext_iff.mp hs ⟨d, hd⟩)
    exact hgt.not_ge hl

lemma chromatic_graph (L : Lvl) (hL : Ok L) :
    (graph L).chromaticCardinal = ℵ₁ := by
  classical
  let proper : (graph L).Coloring Level :=
    SimpleGraph.Coloring.mk (fun u => nlab L u.val) (fun h => h.2)
  have hn : ({κ : Cardinal | ∃ (C : Type) (_ : #C = κ),
      Nonempty ((graph L).Coloring C)}).Nonempty :=
    ⟨_, Level, rfl, ⟨proper⟩⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) ⟨Level, level_size, ⟨proper⟩⟩
  · apply le_csInf hn
    rintro _ ⟨C, rfl, ⟨c⟩⟩
    by_contra! h
    have hC : #C ≤ ℵ₀ := by simpa [Cardinal.aleph_one_le_iff] using not_le.mpr h
    obtain ⟨g⟩ := (Cardinal.le_def C ℕ).mp (by simpa using hC)
    exact not_colorable_nat L hL
      (SimpleGraph.Coloring.mk (g ∘ c) (fun h he => c.valid h (g.injective he)))

section finite
variable {X : Type}

lemma colour_exists (s : ℕ) : ∀ (j : ℕ) (B : Finset (List X)),
    ∃ χ : List X → Bool, ∀ (v : List X) (F : Finset X),
      (∀ x ∈ F, x :: v.take j ∈ B ∧ v.take (j+1) ∈ B ∧
        χ (x :: v.take j) = χ (v.take (j+1))) →
      F.card ≤ s ∨ F.card * s ^ j ≤ B.card := by
  classical
  intro j
  induction j with
  | zero =>
    intro B
    refine ⟨fun _ => false, fun v F hF => Or.inr ?_⟩
    simp only [pow_zero, mul_one]
    refine Finset.card_le_card_of_injOn (fun x => [x]) ?_ ?_
    · intro x hx
      simpa using (hF x hx).1
    · intro x _ y _ h
      simpa using h
  | succ j ih =>
    intro B
    let B0 : Finset (List X) := B.filter (fun u => u ≠ [])
    let cnt : List X → ℕ := fun p => (B0.filter (fun u => u.tail = p)).card
    let B' : Finset (List X) := (B0.image List.tail).filter (fun p => s ≤ cnt p)
    have hB' : B'.card * s ≤ B.card := by
      calc B'.card * s = ∑ _p ∈ B', s := by simp
        _ ≤ ∑ p ∈ B', cnt p := Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp hp).2)
        _ = (B0.filter (fun u => u.tail ∈ B')).card :=
            Finset.sum_card_fiberwise_eq_card_filter _ _ _
        _ ≤ B0.card := Finset.card_filter_le _ _
        _ ≤ B.card := Finset.card_filter_le _ _
    obtain ⟨χ', hχ'⟩ := ih B'
    refine ⟨fun u => if u.take (j+1) ∈ B' then χ' (u.take (j+1)) else
        if u.tail ∈ B' then !χ' u.tail else false, fun v F hF => ?_⟩
    by_cases hp : v.take (j+1) ∈ B'
    · have key : ∀ x ∈ F, x :: v.take j ∈ B' ∧ v.take (j+1) ∈ B' ∧
          χ' (x :: v.take j) = χ' (v.take (j+1)) := by
        intro x hx
        have h := (hF x hx).2.2
        have e1 : (v.take (j+1+1)).take (j+1) = v.take (j+1) := by
          rw [List.take_take]; congr 1; omega
        have e2 : (x :: v.take (j+1)).take (j+1) = x :: v.take j := by
          rw [List.take_succ_cons, List.take_take]; congr 2; omega
        simp only [e1, e2, hp, if_true, List.tail_cons] at h
        by_cases hx' : x :: v.take j ∈ B'
        · simp only [hx', if_true] at h
          exact ⟨hx', hp, h⟩
        · simp only [hx', if_false] at h
          exact absurd h (by cases χ' (v.take (j+1)) <;> simp)
      rcases hχ' v F key with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        calc F.card * s ^ (j+1) = F.card * s ^ j * s := by ring
          _ ≤ B'.card * s := Nat.mul_le_mul_right s h
          _ ≤ B.card := hB'
    · refine Or.inl ?_
      by_contra hle
      rw [not_le] at hle
      have hinj : F.card ≤ cnt (v.take (j+1)) := by
        refine Finset.card_le_card_of_injOn (fun x => x :: v.take (j+1)) ?_ ?_
        · intro x hx
          have h := (hF x hx).1
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h, by simp⟩, by simp⟩
        · intro x _ y _ h
          simpa using h
      have hne : F.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      apply hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x :: v.take (j+1), ?_, by simp⟩, by omega⟩
      exact Finset.mem_filter.mpr ⟨(hF x hx).1, by simp⟩

lemma cons_headI_tail' [Inhabited X] (l : List X) (h : l ≠ []) : l.headI :: l.tail = l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

lemma deletion_bound {V : Type} [Inhabited X] (G : SimpleGraph V) (val : V → List X) (j : ℕ)
    (hval : Function.Injective val) (hlen : ∀ a, (val a).length = j + 1)
    (hadj : ∀ a b, G.Adj a b →
      (val a).tail = (val b).dropLast ∨ (val b).tail = (val a).dropLast)
    (S : Set V) [Fintype S] (s : ℕ) (hs : Fintype.card S ≤ s ^ (j + 1)) (hs1 : 1 ≤ s) :
    Erdos111.bipartiteDistance (G.induce S) ≤ Fintype.card S * s := by
  classical
  let n := Fintype.card S
  let B : Finset (List X) := Finset.univ.image (fun a : S => val a.val)
  have hB : B.card ≤ n := by
    simpa [n] using (Finset.card_image_le (s := (Finset.univ : Finset S)) (f := fun a : S => val a.val))
  obtain ⟨χ, hχ⟩ := colour_exists s j B
  let color (a : S) : Bool := χ (val a.val)
  let bad (b : S) := Finset.univ.filter
    (fun a : S => (val a.val).tail = (val b.val).dropLast ∧ color a = color b)
  have hne : ∀ a : S, val a.val ≠ [] := by
    intro a h
    have := hlen a.val
    rw [h] at this
    simp at this
  have bad_le (b : S) : (bad b).card ≤ s := by
    let F : Finset X := (bad b).image (fun a => (val a.val).headI)
    have hF : F.card = (bad b).card := by
      refine Finset.card_image_of_injOn ?_
      intro a ha a' ha' h
      have h1 := (Finset.mem_filter.mp ha).2.1
      have h2 := (Finset.mem_filter.mp ha').2.1
      have e : val a.val = val a'.val := by
        rw [← cons_headI_tail' _ (hne a), ← cons_headI_tail' _ (hne a'), h1, h2]
        exact congrArg (· :: (val b.val).dropLast) h
      exact Subtype.ext (hval e)
    have hdl : (val b.val).dropLast = (val b.val).take j := by
      rw [List.dropLast_eq_take, hlen]; rfl
    have htk : (val b.val).take (j + 1) = val b.val :=
      List.take_of_length_le (by rw [hlen])
    have hmemB : ∀ a : S, val a.val ∈ B := fun a =>
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have key := hχ (val b.val) F (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have h1 := (Finset.mem_filter.mp ha).2
      have e : (val a.val).headI :: (val b.val).take j = val a.val := by
        rw [← hdl, ← h1.1]; exact cons_headI_tail' _ (hne a)
      rw [e, htk]
      exact ⟨hmemB a, hmemB b, h1.2⟩)
    rw [hF] at key
    rcases key with h | h
    · exact h
    · have h3 : (bad b).card * s ^ j ≤ s * s ^ j := by
        calc (bad b).card * s ^ j ≤ B.card := h
          _ ≤ n := hB
          _ ≤ s ^ (j + 1) := hs
          _ = s * s ^ j := by ring
      exact Nat.le_of_mul_le_mul_right h3 (Nat.pow_pos (by omega))
  let G' := G.induce S
  let H : SimpleGraph S :=
    { Adj := fun a b => G'.Adj a b ∧ color a ≠ color b
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun _ h => h.2 rfl⟩ }
  let pairs (b : S) := (bad b).image (fun a => s(a, b))
  let U := Finset.univ.biUnion pairs
  have contains : G'.edgeSet \ H.edgeSet ⊆ (U : Set (Sym2 S)) := by
    intro p
    induction p using Sym2.inductionOn with
    | _ a b =>
      rintro ⟨hg, hh⟩
      have hc : color a = color b := by
        by_contra h
        exact hh (show H.Adj a b from ⟨hg, h⟩)
      rcases hadj a.val b.val (show G.Adj a.val b.val from hg) with hd | hd
      · exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hc⟩, rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hc.symm⟩,
            Sym2.eq_swap⟩⟩
  have count : (G'.edgeSet \ H.edgeSet).ncard ≤ n * s := calc
    _ ≤ (U : Set (Sym2 S)).ncard := Set.ncard_le_ncard contains
    _ = U.card := Set.ncard_coe_finset _
    _ ≤ ∑ b : S, (pairs b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : S, s := Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (bad_le b))
    _ = n * s := by simp [n]
  apply le_trans (b := (G'.edgeSet \ H.edgeSet).ncard) _ count
  unfold Erdos111.bipartiteDistance
  apply Nat.sInf_le
  refine ⟨H, fun _ _ h => h.1, ⟨SimpleGraph.Coloring.mk
    (fun a => if color a then (1 : Fin 2) else 0) (fun {a b} h => ?_)⟩, rfl⟩
  have h2 : color a ≠ color b := h.2
  cases ha : color a <;> cases hb : color b <;> simp_all

end finite

lemma bound_hG (L : Lvl) (s m : ℕ) (hm : 1 ≤ m) (hs : m ≤ s ^ (L.rank + 1 + 1))
    (hs1 : 1 ≤ s) : Erdos111.hG (graph L) m ≤ m * s := by
  unfold Erdos111.hG
  apply csSup_le'
  rintro k ⟨S, hS, rfl⟩
  let : Fintype S := (Set.finite_of_ncard_pos (show 0 < S.ncard by omega)).fintype
  have hcard : Fintype.card S = m := by
    rw [← hS, Set.fintypeCard_eq_ncard]
  have h := deletion_bound (X := Set L.Z) (graph L) (fun a : W L => a.val) (L.rank + 1)
    (fun a b hab => Subtype.ext hab) (fun a => a.property.1) (fun a b hab => hab.1) S s
    (by rw [hcard]; exact hs) hs1
  rw [hcard] at h
  exact h

lemma asymp (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hn : 1 ≤ ε * ((n : ℝ) + 2)) :
    (fun m : ℕ => (Erdos111.hG (graph (tower n)) m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (1 + ε)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with m hm
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hpow1 : (1 : ℝ) ≤ (m : ℝ) ^ ε := Real.one_le_rpow hm1 hε.le
  have hs1 : 1 ≤ ⌈(m : ℝ) ^ ε⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hsle : ((⌈(m : ℝ) ^ ε⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) ^ ε + 1 :=
    (Nat.ceil_lt_add_one (by linarith)).le
  have hsge : (m : ℝ) ^ ε ≤ ((⌈(m : ℝ) ^ ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hs : m ≤ ⌈(m : ℝ) ^ ε⌉₊ ^ ((tower n).rank + 1 + 1) := by
    rw [tower_rank]
    have h1 : (m : ℝ) ≤ ((m : ℝ) ^ ε) ^ (n + 1 + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (m : ℝ) ^ (ε * ((n + 1 + 1 : ℕ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le hm1
          push_cast
          linarith
    have h2 : ((m : ℝ) ^ ε) ^ (n + 1 + 1) ≤ ((⌈(m : ℝ) ^ ε⌉₊ : ℕ) : ℝ) ^ (n + 1 + 1) :=
      pow_le_pow_left₀ (by linarith) hsge _
    exact_mod_cast h1.trans h2
  have hb := bound_hG (tower n) ⌈(m : ℝ) ^ ε⌉₊ m hm hs hs1
  have hb2 : (Erdos111.hG (graph (tower n)) m : ℝ) ≤ (m : ℝ) * ((⌈(m : ℝ) ^ ε⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hb
  calc (Erdos111.hG (graph (tower n)) m : ℝ) ≤ (m : ℝ) * ((⌈(m : ℝ) ^ ε⌉₊ : ℕ) : ℝ) := hb2
    _ ≤ (m : ℝ) * ((m : ℝ) ^ ε + (m : ℝ) ^ ε) := by gcongr; linarith
    _ = 2 * ((m : ℝ) * (m : ℝ) ^ ε) := by ring
    _ = 2 * (m : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hmpos, Real.rpow_one]

end OMA.E111c

theorem OMA.solution : type_of% @Erdos111.erdos_111.variants.erdos_conjecture := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have h1 : 1 ≤ ε * ((n : ℝ) + 2) := by
    have h2 : 1 / ε * ε = 1 := by field_simp
    nlinarith
  exact ⟨OMA.E111c.W (OMA.E111c.tower n), OMA.E111c.graph (OMA.E111c.tower n),
    OMA.E111c.chromatic_graph _ (OMA.E111c.tower_ok n), OMA.E111c.asymp n ε hε h1⟩
