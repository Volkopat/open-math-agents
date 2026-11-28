import OMAStatements.S_arxiv_1805_10646

open OMA.S_arxiv_1805_10646

/-!
# Palindromes in three-branch binary trees

The statement and the attaining construction are from Amy Glen, Jamie Simpson
and W. F. Smyth, *Palindromes in starlike trees*, arXiv:1805.10646.
The upper bound follows by comparing palindromic factors on the three leaf paths.
Lean proof by @DrSubspace.
-/

namespace StarlikePalindromes

private abbrev zeros (n : ℕ) := List.replicate n false
private abbrev ones (n : ℕ) := List.replicate n true
private def block (a b c : ℕ) := zeros a ++ (ones b ++ zeros c)

/-- Every factor of a three-run word is a (possibly truncated) three-run word. -/
private lemma factor_block {w : List Bool} {a b c : ℕ} (hb : 0 < b)
    (h : w <:+: block a b c) :
    ∃ i j l, w = block i j l ∧ i ≤ a ∧ j ≤ b ∧ l ≤ c ∧
      (0 < i → 0 < l → j = b) ∧ (j = 0 → i = 0 ∨ l = 0) := by
  obtain ⟨pre, post, he⟩ := h
  have he' : ((block a b c).drop pre.length).take w.length = w := by
    rw [← he, List.append_assoc, List.drop_append_length, List.take_append_length]
  simp only [block, List.drop_append, List.take_append, List.drop_replicate,
    List.take_replicate, List.length_replicate] at he'
  exact ⟨_, _, _, he'.symm, by omega, by omega, by omega, by omega, by omega⟩

private lemma first_one (a b c : ℕ) : (block a (b+1) c).idxOf true = a := by
  induction a with
  | zero => simp [block, List.replicate_succ]
  | succ a ih =>
    change (false :: block a (b+1) c).idxOf true = a+1
    simp [ih]

private lemma symmetric_flanks {i j l : ℕ} (hj : 0 < j)
    (h : (block i j l).reverse = block i j l) : i = l := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hh : block l (b+1) i = block i (b+1) l := by
    simpa [block, List.append_assoc] using h
  have := congrArg (List.idxOf true) hh
  simpa [first_one] using this.symm

private abbrev Index (t : ℕ) := (Fin (t+2) ⊕ Fin (t+2)) ⊕ (Fin (t+1) ⊕ Fin (t+1))

private def encode {t : ℕ} : Index t → List Bool
  | .inl (.inl i) => zeros (i.val+1)
  | .inl (.inr i) => block i 1 i
  | .inr (.inl i) => block i 2 i
  | .inr (.inr i) => block i 3 i

private lemma encode_inj (t : ℕ) : Function.Injective (@encode t) := by
  rintro ((i|i)|(i|i)) ((h|h)|(h|h)) eqn <;>
    have h₁ := congrArg (List.count true) eqn <;>
    have h₂ := congrArg List.length eqn <;>
    simp [encode, block, List.count_replicate] at h₁ h₂ <;>
    simp_all <;> apply Fin.ext <;> omega

private def x (t : ℕ) := zeros (t+2)
private def y (t : ℕ) := ones 1 ++ zeros (t+1)
private def z (t : ℕ) := ones 2 ++ zeros t

private lemma paths (t : ℕ) : leafPaths (x t) (y t) (z t) =
    [block (t+2) 1 (t+1), block (t+2) 2 t, block (t+1) 3 t] := by
  simp [leafPaths,x,y,z,block,List.append_assoc]
  rfl

private lemma block_infix {i a b c : ℕ} (ha : i ≤ a) (hc : i ≤ c) :
    block i b i <:+: block a b c := by
  refine ⟨zeros (a-i), zeros (c-i), ?_⟩
  simp only [block, List.append_assoc]
  rw [← List.append_assoc (zeros _), ← List.replicate_add, show a-i+i=a by omega,
    ← List.replicate_add, show i+(c-i)=c by omega]

private lemma classify {p : List Bool} {t a b c : ℕ} (ha : a ≤ t+2) (hc : c ≤ t+1)
    (hb : 0 < b) (hb' : b ≤ 3) (hs : b = 1 ∨ c ≤ t)
    (hne : p ≠ []) (hp : p.reverse = p) (h : p <:+: block a b c) :
    p ∈ Set.range (@encode t) := by
  obtain ⟨i,j,l, rfl, hi,hj,hl, hm, he⟩ := factor_block hb h
  by_cases h0 : j = 0
  · subst j
    have hh : block i 0 l = zeros (i+l) := by simp [block]
    have hsum : 0 < i+l := by
      by_contra! h
      rw [hh, show i+l=0 by omega] at hne
      exact hne rfl
    refine ⟨.inl (.inl ⟨i+l-1, by rcases he rfl with h|h <;> omega⟩), ?_⟩
    simp only [encode, hh, show i+l-1+1=i+l by omega]
  have hil := symmetric_flanks (by omega : 0 < j) hp
  subst l
  have hlim : 1 < j → i ≤ t := by
    intro hj'
    by_cases hi0 : i = 0
    · omega
    · have := hm (by omega) (by omega)
      omega
  have : j ≤ 3 := by omega
  interval_cases j
  all_goals first
    | contradiction
    | exact ⟨.inl (.inr ⟨i, by omega⟩), rfl⟩
    | exact ⟨.inr (.inl ⟨i, by have := hlim (by decide); omega⟩), rfl⟩
    | exact ⟨.inr (.inr ⟨i, by have := hlim (by decide); omega⟩), rfl⟩

private lemma encoded_pal (t : ℕ) (q : Index t) :
    encode q ∈ palindromes (x t) (y t) (z t) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases q with ((i|i)|(i|i)) <;> simp [encode,block]
  · rcases q with ((i|i)|(i|i)) <;> simp [encode,block,List.append_assoc] <;> rfl
  · rw [paths]
    rcases q with ((i|i)|(i|i))
    · refine ⟨block (t+2) 1 (t+1), by simp, ?_⟩
      apply List.infix_append_of_infix_left
      apply List.infix_replicate_iff.mpr
      simp [encode]
      omega
    · exact ⟨_, List.mem_cons_self, block_infix (by have := i.isLt; omega) (by have := i.isLt; omega)⟩
    · exact ⟨block (t+2) 2 t, by simp, block_infix (by have := i.isLt; omega) (by have := i.isLt; omega)⟩
    · exact ⟨block (t+1) 3 t, by simp, block_infix (by have := i.isLt; omega) (by have := i.isLt; omega)⟩

/-- The explicit construction of Glen, Simpson and Smyth attains the proposed maximum. -/
theorem attainable (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y z : List Bool, x.length = n ∧ y.length = n ∧ z.length = n ∧
      (palindromes x y z).ncard = 4*n-2 := by
  obtain ⟨t,rfl⟩ : ∃ t, n = t+2 := ⟨n-2, by omega⟩
  refine ⟨x t, y t, z t, by simp [x], by simp [y], by simp [z]; omega, ?_⟩
  have he : palindromes (x t) (y t) (z t) = Set.range (@encode t) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hn,hp,w,hw,hi⟩
      rw [paths] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl|rfl|rfl <;> apply classify (by omega) (by omega) (by decide)
        (by decide) (by omega) hn hp hi
    · rintro _ ⟨q,rfl⟩
      exact encoded_pal t q
  rw [he, Set.ncard_range_of_injective (encode_inj t)]
  simp [Index]
  omega

/-- Distinct nonempty palindromic factors of a word. -/
def pals (w : List Bool) : Finset (List Bool) :=
  w.sublists.toFinset.filter fun p => p ≠ [] ∧ p.reverse = p ∧ p <:+: w

@[simp] private lemma mem_pals {p w : List Bool} :
    p ∈ pals w ↔ p ≠ [] ∧ p.reverse = p ∧ p <:+: w := by
  simp only [pals, Finset.mem_filter, List.mem_toFinset, List.mem_sublists]
  exact ⟨And.right, fun h => ⟨h.2.2.sublist, h⟩⟩

private lemma reverse_pals (w : List Bool) : pals w.reverse = pals w := by
  ext p
  simp only [mem_pals]
  constructor <;> rintro ⟨hp,hr,hi⟩ <;> refine ⟨hp,hr,?_⟩
  · simpa [hr] using List.reverse_infix.mpr hi
  · simpa [hr] using List.reverse_infix.mpr hi

private lemma pals_mono {w v : List Bool} (h : w <:+: v) : pals w ⊆ pals v := by
  intro p hp
  obtain ⟨hne,hr,hi⟩ := mem_pals.mp hp
  exact mem_pals.mpr ⟨hne,hr,hi.trans h⟩

private lemma short_prefix {a : Bool} {u p q : List Bool}
    (h : p <:+ q) (hq : q <+: a::u) : p = q ∨ p <:+: u := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht⟩ := hq
  cases s with
  | nil => exact Or.inl (by simpa using hs)
  | cons b bs =>
    rw [← hs] at ht
    exact Or.inr ⟨bs,t,by simpa using congrArg List.tail ht⟩

private lemma one_new (a : Bool) (w : List Bool) :
    (pals (a::w) \ pals w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  have aux (p q : List Bool) (hp : p ∈ pals (a::w) \ pals w)
      (hq : q ∈ pals (a::w) \ pals w) (hlen : p.length ≤ q.length) : p = q := by
    have read (x : List Bool) (h : x ∈ pals (a::w) \ pals w) :
        x.reverse = x ∧ x <+: a::w ∧ ¬ x <:+: w := by
      obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp h
      obtain ⟨he,hr,hi⟩ := mem_pals.mp hp
      have hno : ¬ x <:+: w := fun hh => hn (mem_pals.mpr ⟨he,hr,hh⟩)
      exact ⟨hr, (List.infix_cons_iff.mp hi).resolve_right hno, hno⟩
    obtain ⟨hr,hpp,hn⟩ := read p hp
    obtain ⟨hs,hqq,_⟩ := read q hq
    have h := List.reverse_suffix.mpr (List.prefix_of_prefix_length_le hpp hqq hlen)
    rw [hr,hs] at h
    exact (short_prefix h hqq).resolve_right hn
  intro p hp q hq
  rcases le_total p.length q.length with h|h
  · exact aux p q hp hq h
  · exact (aux q p hq hp h).symm

private lemma diff_triangle (A B C : Finset (List Bool)) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  apply (Finset.card_le_card (t := (A \ B) ∪ (B \ C)) ?_).trans (Finset.card_union_le ..)
  intro p hp
  simp only [Finset.mem_sdiff, Finset.mem_union] at *
  tauto

private lemma extension (u v : List Bool) :
    (pals (u++v) \ pals v).card ≤ u.length := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have h := diff_triangle (pals (a::(u++v))) (pals (u++v)) (pals v)
    have h₁ := one_new a (u++v)
    simp only [List.cons_append, List.length_cons]
    omega

private lemma length_bound (w : List Bool) : (pals w).card ≤ w.length := by
  have h : pals [] = ∅ := by ext p; simp; tauto
  simpa [h] using extension w []

/-- Palindromes on the path joining the leaves of two arms. -/
def pairPals (u v : List Bool) := pals (u.reverse ++ v)

private lemma pair_symm (u v : List Bool) : pairPals u v = pairPals v u := by
  unfold pairPals
  rw [← reverse_pals (u.reverse ++ v)]
  simp

private lemma tree_card (x y z : List Bool) :
    (palindromes x y z).ncard = (pairPals x y ∪ pairPals x z ∪ pairPals y z).card := by
  have h : palindromes x y z = (↑(pairPals x y ∪ pairPals x z ∪ pairPals y z) : Set _) := by
    ext p
    simp [palindromes,leafPaths,pairPals]
    tauto
  rw [h, Set.ncard_coe_finset]

/-- If the new arm repeats a prefix from either existing arm, its associated path
has already contributed the palindromes from the common prefix. -/
private lemma shared_prefix {base other common u v : List Bool}
    (h : other = common ++ u) :
    (pairPals (common++v) base \ pairPals other base).card ≤ v.length := by
  subst other
  have hsub : pairPals common base ⊆ pairPals (common++u) base := by
    apply pals_mono
    simpa [List.append_assoc] using
      (List.infix_append_right (l₁ := u.reverse) (l₂ := common.reverse ++ base))
  have hdiff : pairPals (common++v) base \ pairPals (common++u) base ⊆
      pairPals (common++v) base \ pairPals common base := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨h₁,fun hc => h₂ (hsub hc)⟩
  apply (Finset.card_le_card hdiff).trans
  simpa [pairPals,List.append_assoc] using extension v.reverse (common.reverse++base)

/-- A common prefix with each of the other two arms saves one slot per letter. -/
theorem prefix_bound {x y z p q a b c d : List Bool}
    (hx : x = p ++ a) (hz : z = p ++ b) (hy : y = q ++ c) (hz' : z = q ++ d) :
    (palindromes x y z).ncard ≤ x.length + y.length + b.length + d.length := by
  have h₁ := shared_prefix (base := y) (v := b) hx
  have h₂ := shared_prefix (base := x) (v := d) hy
  rw [← hz, pair_symm z y] at h₁
  rw [← hz', pair_symm z x, pair_symm y x] at h₂
  have h₃ : (pairPals x y).card ≤ x.length+y.length := by
    simpa [pairPals] using length_bound (x.reverse++y)
  rw [tree_card]
  have hsub : pairPals x y ∪ pairPals x z ∪ pairPals y z ⊆
      pairPals x y ∪ (pairPals x z \ pairPals x y) ∪ (pairPals y z \ pairPals x y) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  have h₄ := Finset.card_le_card hsub
  have h₅ := Finset.card_union_le (pairPals x y) (pairPals x z \ pairPals x y)
  have h₆ := Finset.card_union_le (pairPals x y ∪ (pairPals x z \ pairPals x y)) (pairPals y z \ pairPals x y)
  omega

private lemma swap_first (x y z : List Bool) :
    (palindromes x y z).ncard = (palindromes y x z).ncard := by
  rw [tree_card, tree_card, pair_symm y x]
  congr 1
  ext p
  simp only [Finset.mem_union]
  tauto

private lemma swap_last (x y z : List Bool) :
    (palindromes x y z).ncard = (palindromes x z y).ncard := by
  rw [tree_card, tree_card, pair_symm z y]
  congr 1
  ext p
  simp only [Finset.mem_union]
  tauto

private lemma middle_shared {x z y : List Bool} {a : Bool} (n : ℕ)
    (hx : x.length+1 = n) (hy : y.length = n) (hz : z.length+1 = n) :
    (palindromes (a::x) y (a::z)).ncard ≤ 4*n-1 := by
  have h := prefix_bound (x := a::x) (y := y) (z := a::z)
    (p := [a]) (q := []) (a := x) (b := z) (c := y) (d := a::z) rfl rfl rfl rfl
  simp only [List.length_cons] at h
  omega

/-- The upper estimate of Glen, Simpson and Smyth, one above the sharp bound. -/
theorem upper_within_one {x y z : List Bool} {n : ℕ} (hn : 2 ≤ n)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n) :
    (palindromes x y z).ncard ≤ 4*n-1 := by
  cases x with
  | nil => simp at hx; omega
  | cons a x =>
    cases y with
    | nil => simp at hy; omega
    | cons b y =>
      cases z with
      | nil => simp at hz; omega
      | cons c z =>
        by_cases hac : a = c
        · subst c; exact middle_shared n hx hy hz
        by_cases hab : a = b
        · subst b
          rw [swap_last]
          exact middle_shared n hx hz hy
        have hbc : b = c := by cases a <;> cases b <;> cases c <;> simp_all
        subst c
        rw [swap_first]
        exact middle_shared n hy hx hz

/-- Two shared prefix letters, counted across the two pairs, suffice for the conjectured bound. -/
theorem upper_of_prefixes {x y z p q a b c d : List Bool} {n : ℕ}
    (hxn : x.length = n) (hyn : y.length = n) (hzn : z.length = n)
    (hx : x = p ++ a) (hz : z = p ++ b) (hy : y = q ++ c) (hz' : z = q ++ d)
    (hshare : 2 ≤ p.length + q.length) :
    (palindromes x y z).ncard ≤ 4*n-2 := by
  have h := prefix_bound hx hz hy hz'
  have h₁ := congrArg List.length hz
  have h₂ := congrArg List.length hz'
  simp only [List.length_append] at h₁ h₂
  omega

private lemma own_pals (u v : List Bool) : pals u ⊆ pairPals u v := by
  rw [← reverse_pals u]
  exact pals_mono List.infix_append_left

private lemma new_on_pair (u v : List Bool) :
    (pairPals u v \ pals u).card ≤ v.length := by
  rw [pair_symm]
  simpa [pairPals] using extension v.reverse u

private lemma outside_both (u v : List Bool) :
    (pairPals u v \ (pals u ∪ pals v)).card + (pals v \ pals u).card ≤ v.length := by
  let A := pairPals u v \ (pals u ∪ pals v)
  let B := pals v \ pals u
  have hsub : A ∪ B ⊆ pairPals u v \ pals u := by
    intro p hp
    have hv : pals v ⊆ pairPals u v := by rw [pair_symm]; exact own_pals _ _
    simp only [A,B,Finset.mem_union,Finset.mem_sdiff] at hp ⊢
    rcases hp with h|h
    · tauto
    · exact ⟨hv h.1,h.2⟩
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mp hb).1)
  have := (Finset.card_le_card hsub).trans (new_on_pair u v)
  rwa [Finset.card_union_of_disjoint hd] at this

private lemma tree_via_crossing {a : Bool} {u v w : List Bool} {n : ℕ}
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n) :
    (palindromes (a::u) w (a::v)).ncard ≤ 2*n + v.length +
      (pairPals (a::u) (a::v) \ (pals (a::u) ∪ pals (a::v))).card := by
  let U := a::u
  let V := a::v
  let A := pairPals U w
  let B := pairPals V w
  let C := pairPals U V
  have ha : A.card ≤ 2*n := by
    have h := length_bound (U.reverse++w)
    have hlen : (U.reverse++w).length = 2*n := by
      rw [List.length_append, List.length_reverse, show U.length=n from hu, hw, two_mul]
    rwa [hlen] at h
  have hb : (B \ A).card ≤ v.length :=
    shared_prefix (base := w) (other := U) (common := [a]) (u := u) (v := v) rfl
  have sub : C \ (B ∪ A) ⊆ C \ (pals U ∪ pals V) := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hp
    refine Finset.mem_sdiff.mpr ⟨h₁,?_⟩
    intro h
    apply h₂
    rcases Finset.mem_union.mp h with h|h
    · exact Finset.mem_union_right _ (own_pals U w h)
    · exact Finset.mem_union_left _ (own_pals V w h)
  have hmono := Finset.card_le_card sub
  have hAB := Finset.card_sdiff_add_card B A
  have hABC := Finset.card_sdiff_add_card C (B ∪ A)
  have heq : (palindromes U w V).ncard = (C ∪ (B ∪ A)).card := by
    rw [tree_card, pair_symm w V]
    simp [A,B,C,Finset.union_comm,Finset.union_left_comm]
  change (palindromes U w V).ncard ≤ 2*n + v.length + (C \ (pals U ∪ pals V)).card
  rw [heq]
  omega

private lemma improved {a : Bool} {u v w : List Bool} {n : ℕ}
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n) :
    (palindromes (a::u) w (a::v)).ncard + (pals (a::v) \ pals (a::u)).card ≤ 4*n-1 := by
  have h := tree_via_crossing hu hv hw
  have hc := outside_both (a::u) (a::v)
  simp only [List.length_cons] at hv hc
  omega

/-- Any violation forces the two same-initial-letter arms to have identical sets of
palindromic factors, even though the arms can start with different two-letter words. -/
theorem upper_of_distinct_factors {a : Bool} {u v w : List Bool} {n : ℕ}
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n)
    (hne : ∃ p, (p ≠ [] ∧ p.reverse = p) ∧ ¬ (p <:+: a::u ↔ p <:+: a::v)) :
    (palindromes (a::u) w (a::v)).ncard ≤ 4*n-2 := by
  obtain ⟨p,⟨hp,hr⟩,hne⟩ := hne
  by_cases hi : p <:+: a::u
  · have hni : ¬ p <:+: a::v := by tauto
    have hm : p ∈ pals (a::u) \ pals (a::v) := by simp [hp,hr,hi,hni]
    have hc := Finset.card_pos.mpr ⟨p,hm⟩
    have h := improved hv hu hw
    rw [swap_first (a::v) w (a::u), swap_last w (a::v) (a::u),
      ← swap_first (a::u) w (a::v)] at h
    omega
  · have hj : p <:+: a::v := by tauto
    have hm : p ∈ pals (a::v) \ pals (a::u) := by simp [hp,hr,hi,hj]
    have hc := Finset.card_pos.mpr ⟨p,hm⟩
    have h := improved hu hv hw
    omega

/-- The only remaining pairs of same-initial-letter branches must contribute one
new palindrome per letter when joined, even after discarding the palindromes
already inside either branch. -/
theorem upper_of_fewer_crossing {a : Bool} {u v w : List Bool} {n : ℕ}
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n)
    (hcross : (pairPals (a::u) (a::v) \ (pals (a::u) ∪ pals (a::v))).card < n) :
    (palindromes (a::u) w (a::v)).ncard ≤ 4*n-2 := by
  have h := tree_via_crossing hu hv hw
  simp only [List.length_cons] at hv
  omega

private def Rich (w : List Bool) := (pals w).card = w.length

private lemma rich_reverse {w : List Bool} : Rich w.reverse ↔ Rich w := by
  simp [Rich, reverse_pals]

private lemma rich_right {u v : List Bool} (h : Rich (u++v)) : Rich v := by
  have hcard := Finset.card_sdiff_add_card_eq_card (pals_mono (List.infix_append_right (l₁ := u) (l₂ := v)))
  have hdiff := extension u v
  have hb := length_bound v
  unfold Rich at *
  rw [List.length_append] at h
  omega

private lemma rich_left {u v : List Bool} (h : Rich (u++v)) : Rich u := by
  have h' := rich_reverse.mpr h
  rw [List.reverse_append] at h'
  exact rich_reverse.mp (rich_right h')

private lemma rich_factor {u w : List Bool} (hw : Rich w) (hu : u <:+: w) : Rich u := by
  obtain ⟨l,r,rfl⟩ := hu
  exact rich_left (rich_right (by simpa [List.append_assoc] using hw : Rich (l++(u++r))))

private lemma orient_trim (pre v u : List Bool) (hr : Rich (pre++v))
    (hu : u <:+: pre++v) (hc : pals u ⊆ pals v) : u <:+: v ∨ u.reverse <:+: v := by
  induction pre generalizing u with
  | nil => exact Or.inl (by simpa using hu)
  | cons a pre ih =>
    let t := pre++v
    have hr' : Rich t := rich_right (u := [a]) hr
    have hh : u <:+: t ∨ u.reverse <:+: t := by
      rcases List.infix_cons_iff.mp hu with hp|hi
      · have larger : (pals t).card < (pals (a::t)).card := by
          change (pals (a::t)).card = (a::t).length at hr
          change (pals t).card = t.length at hr'
          simp [hr,hr']
        obtain ⟨p,hw,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card larger
        obtain ⟨hn,hrev,hin⟩ := mem_pals.mp hw
        have notin : ¬ p <:+: t := fun h => ht (mem_pals.mpr ⟨hn,hrev,h⟩)
        have pref : p <+: a::t := (List.infix_cons_iff.mp hin).resolve_right notin
        have big : u.length < p.length := by
          by_contra! h
          have hpu := List.prefix_of_prefix_length_le pref hp h
          exact ht (pals_mono (List.infix_append_right (l₁ := pre) (l₂ := v))
            (hc (mem_pals.mpr ⟨hn,hrev,hpu.isInfix⟩)))
        have hup := List.prefix_of_prefix_length_le hp pref big.le
        have hsu := List.reverse_suffix.mpr hup
        rw [hrev] at hsu
        refine Or.inr ((short_prefix hsu pref).resolve_left ?_)
        intro he
        have := congrArg List.length he
        simp at this
        omega
      · exact Or.inl hi
    rcases hh with h|h
    · exact ih u hr' h hc
    · have he := ih u.reverse hr' h (by simpa [reverse_pals] using hc)
      simpa [or_comm] using he

/-- Within a rich word, containment of palindrome sets forces containment of a
factor in one of its two orientations. -/
theorem containment {w u v : List Bool} (hw : Rich w) (hu : u <:+: w) (hv : v <:+: w)
    (hc : pals u ⊆ pals v) : u <:+: v ∨ u.reverse <:+: v := by
  obtain ⟨l,r,rfl⟩ := hv
  rw [List.append_assoc] at hw hu
  have h := orient_trim l (v++r) u hw hu (hc.trans (pals_mono List.infix_append_left))
  have hr := rich_reverse.mpr (rich_right hw)
  rw [List.reverse_append] at hr
  have aux (s : List Bool) (hs : s <:+: v++r) (hp : pals s ⊆ pals v) :
      s <:+: v ∨ s.reverse <:+: v := by
    have hs' := List.reverse_infix.mpr hs
    rw [List.reverse_append] at hs'
    have ht := orient_trim r.reverse v.reverse s.reverse hr hs' (by simpa [reverse_pals] using hp)
    rcases ht with h|h
    · exact Or.inl (List.reverse_infix.mp h)
    · exact Or.inr (List.reverse_infix.mp h)
  rcases h with h|h
  · exact aux u h hc
  · have ht := aux u.reverse h (by simpa [reverse_pals] using hc)
    simpa [or_comm] using ht

private lemma union_three (A B C : Finset (List Bool)) :
    (A ∪ B ∪ C).card ≤ (A ∪ B).card + (C \ A).card := by
  have hs : C \ (A ∪ B) ⊆ C \ A := by
    intro p hp
    simp only [Finset.mem_sdiff,Finset.mem_union] at *
    tauto
  have h := Finset.card_sdiff_add_card C (A ∪ B)
  rw [Finset.union_comm C] at h
  have := Finset.card_le_card hs
  omega

private lemma critical_counts (E F G : Finset (List Bool)) (n : ℕ)
    (hbad : 4*n-2 < (E ∪ F ∪ G).card)
    (he : E.card ≤ 2*n) (hf : F.card ≤ 2*n) (hg : G.card ≤ 2*n)
    (hfe : (F \ E).card < n) (hef : (E \ F).card < n)
    (hge : (G \ E).card ≤ n) (_hgf : (G \ F).card ≤ n) (heg : (E \ G).card ≤ n) :
    E.card = 2*n ∧ F.card = 2*n ∧ G.card = 2*n ∧
      (E ∩ F).card ≤ n+1 ∧ (E ∩ G).card ≤ n := by
  have u := union_three E F G
  have v := union_three F E G
  rw [Finset.union_comm F E] at v
  have z := union_three E G F
  rw [show E ∪ G ∪ F = E ∪ F ∪ G by ac_rfl] at z
  have e := Finset.card_sdiff_add_card F E
  rw [Finset.union_comm F E] at e
  have f := Finset.card_sdiff_add_card E F
  have g := Finset.card_sdiff_add_card E G
  have uef := Finset.card_union_add_card_inter E F
  have ueg := Finset.card_union_add_card_inter E G
  omega

private lemma cross_diff (u v w : List Bool) :
    (pairPals u v \ pairPals u w).card ≤ v.length := by
  have hsub : pairPals u v \ pairPals u w ⊆ pairPals u v \ pals u := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨h₁,fun h => h₂ (own_pals _ _ h)⟩
  exact (Finset.card_le_card hsub).trans (new_on_pair u v)

private lemma bounded_pair (a b : List Bool) : (pairPals a b).card ≤ a.length+b.length := by
  simpa [pairPals] using length_bound (a.reverse++b)

private lemma common_near_center (a : Bool) (u w : List Bool) :
    (a::w) <:+: (a::u).reverse++w := by
  exact ⟨u.reverse,[],by simp [List.reverse_cons,List.append_assoc]⟩

private lemma extremal_structure {a : Bool} {u v w : List Bool} {n : ℕ}
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n)
    (hbad : 4*n-2 < (palindromes (a::u) w (a::v)).ncard) :
    Rich ((a::u).reverse++w) ∧ Rich ((a::u).reverse++(a::v)) ∧
    pals (a::u) = pals (a::v) ∧ pals (a::u) ⊆ pals (a::w) ∧
    (pairPals (a::u) w ∩ pairPals (a::u) (a::v)).card ≤ n := by
  let U := a::u
  let V := a::v
  let E := pairPals U w
  let F := pairPals V w
  let G := pairPals U V
  have heq : (palindromes U w V).ncard = (E ∪ F ∪ G).card := by
    rw [tree_card,pair_symm w V]
    change (E ∪ G ∪ F).card = _
    congr 1
    ac_rfl
  have hbad' : 4*n-2 < (E ∪ F ∪ G).card := heq ▸ hbad
  have he : E.card ≤ 2*n := by simpa only [hu,hw,two_mul] using bounded_pair (a::u) w
  have hf : F.card ≤ 2*n := by simpa only [hv,hw,two_mul] using bounded_pair (a::v) w
  have hg : G.card ≤ 2*n := by simpa only [hu,hv,two_mul] using bounded_pair (a::u) (a::v)
  have hfe : (F \ E).card ≤ v.length :=
    shared_prefix (base := w) (other := U) (common := [a]) (u := u) (v := v) rfl
  have hef : (E \ F).card ≤ u.length :=
    shared_prefix (base := w) (other := V) (common := [a]) (u := v) (v := u) rfl
  have hgf : (G \ F).card ≤ n := by
    simpa only [← pair_symm U V, show U.length = n from hu] using cross_diff V U w
  obtain ⟨hE,hF,hG,hI,hJ⟩ := critical_counts E F G n hbad' he hf hg
    (by simp only [List.length_cons] at hv; omega)
    (by simp only [List.length_cons] at hu; omega) (hv ▸ cross_diff U V w) hgf (hw ▸ cross_diff U w V)
  have rE : Rich ((a::u).reverse++w) := by
    unfold Rich; rw [List.length_append,List.length_reverse,hu,hw,← two_mul]; exact hE
  have rG : Rich ((a::u).reverse++(a::v)) := by
    unfold Rich; rw [List.length_append,List.length_reverse,hu,hv,← two_mul]; exact hG
  have same : pals U = pals V := by
    ext p
    by_contra h
    have hn : p ≠ [] ∧ p.reverse = p := by
      by_cases hi : p ∈ pals U
      · exact ⟨(mem_pals.mp hi).1,(mem_pals.mp hi).2.1⟩
      · have hj : p ∈ pals V := by tauto
        exact ⟨(mem_pals.mp hj).1,(mem_pals.mp hj).2.1⟩
    have gap : ¬ (p <:+: U ↔ p <:+: V) := by simpa [hn.1,hn.2] using h
    exact (Nat.not_le_of_gt hbad) (upper_of_distinct_factors hu hv hw ⟨p,hn,gap⟩)
  let K := pals (a::w)
  have hk : K ⊆ E ∩ F := Finset.subset_inter
    (pals_mono (common_near_center a u w)) (pals_mono (common_near_center a v w))
  have rK := rich_factor rE (common_near_center a u w)
  have ck : K.card = n+1 := by simpa [K,Rich,hw] using rK
  have hk' : E ∩ F = K := Finset.eq_of_subset_of_card_le hk (by omega) |>.symm
  refine ⟨rE,rG,same,?_,hJ⟩
  change pals U ⊆ K
  rw [← hk']
  exact Finset.subset_inter (own_pals U w) (same ▸ own_pals V w)

private lemma hard_case {a b : Bool} (hab : a ≠ b) (u v w : List Bool) (n : ℕ)
    (hu : (a::a::u).length = n) (hv : (a::b::v).length = n) (hw : (b::w).length = n) :
    (palindromes (a::a::u) (b::w) (a::b::v)).ncard ≤ 4*n-2 := by
  by_contra! bad
  let U := a::a::u
  let V := a::b::v
  let W := b::w
  obtain ⟨rE,rG,hS,hK,hI⟩ := extremal_structure hu hv hw bad
  have neUV : U ≠ V := by simp [U,V,hab]
  have neUW : U ≠ W := by simp [U,W,hab]
  have neVW : V ≠ W := by simp [V,W,hab]
  have rev : U.reverse = V := by
    have hh := containment (u := U.reverse) (v := V) rG List.infix_append_left
      List.infix_append_right (by rw [reverse_pals]; exact hS.le)
    rcases hh with h|h
    · exact h.eq_of_length (by rw [List.length_reverse,show U.length = n from hu,hv])
    · simp only [List.reverse_reverse] at h
      exact False.elim (neUV (h.eq_of_length (hu.trans hv.symm)))
  have hp : V <+: a::W := by
    have hh := containment (u := U.reverse) (v := a::W) rE List.infix_append_left
      (common_near_center a (a::u) W) (by rw [reverse_pals]; exact hK)
    simp only [List.reverse_reverse] at hh
    rw [rev] at hh
    rcases hh with h|h
    · rcases List.infix_cons_iff.mp h with h|h
      · exact h
      · exact False.elim (neVW (h.eq_of_length (hv.trans hw.symm)))
    · rcases List.infix_cons_iff.mp h with h|h
      · have hn : ¬ U <+: a::W := by simp [U,W,hab]
        contradiction
      · exact False.elim (neUW (h.eq_of_length (hu.trans hw.symm)))
  obtain ⟨t,ht⟩ := hp
  have hE : a::V <:+: U.reverse++W := by
    refine ⟨u.reverse,t,?_⟩
    simp only [List.append_assoc,List.cons_append,ht]
    simp [U,List.reverse_cons,List.append_assoc]
  have hG : a::V <:+: U.reverse++V := common_near_center a (a::u) V
  have hsub : pals (a::V) ⊆ pairPals U W ∩ pairPals U V :=
    Finset.subset_inter (pals_mono hE) (pals_mono hG)
  have hlen := rich_factor rE hE
  change (pals (a::V)).card = (a::V).length at hlen
  rw [List.length_cons,show V.length=n from hv] at hlen
  have := (Finset.card_le_card hsub).trans hI
  omega

private lemma swap_outer (x y z : List Bool) :
    (palindromes x y z).ncard = (palindromes z y x).ncard := by
  rw [swap_first x y z,swap_last y x z,← swap_first z y x]

private lemma with_shared_head (a : Bool) (u v w : List Bool) {n : ℕ} (hn : 2 ≤ n)
    (hu : (a::u).length = n) (hv : (a::v).length = n) (hw : w.length = n) :
    (palindromes (a::u) w (a::v)).ncard ≤ 4*n-2 := by
  cases u with
  | nil => simp at hu; omega
  | cons i u =>
    cases v with
    | nil => simp at hv; omega
    | cons j v =>
      cases w with
      | nil => simp at hw; omega
      | cons b w =>
        by_cases h : a = b
        · subst b
          exact upper_of_prefixes hu hw hv (p := [a]) (q := [a])
            (a := i::u) (b := j::v) (c := w) (d := j::v) rfl rfl rfl rfl (by simp)
        by_cases h' : i = j
        · subst j
          exact upper_of_prefixes hu hw hv (p := [a,i]) (q := [])
            (a := u) (b := v) (c := b::w) (d := a::i::v) rfl rfl rfl rfl (by simp)
        have binary : ∀ a b i j : Bool, a ≠ b → i ≠ j →
            (i = a ∧ j = b) ∨ (j = a ∧ i = b) := by decide
        have hcases := binary a b i j h h'
        rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hard_case h u v w n hu hv hw
        · rw [swap_outer]
          exact hard_case h v u w n hv hu hw

theorem upper {x y z : List Bool} {n : ℕ} (hn : 2 ≤ n)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n) :
    (palindromes x y z).ncard ≤ 4*n-2 := by
  cases x with
  | nil => simp at hx; omega
  | cons a x =>
    cases y with
    | nil => simp at hy; omega
    | cons b y =>
      cases z with
      | nil => simp at hz; omega
      | cons c z =>
        by_cases hac : a = c
        · subst c; exact with_shared_head a x z _ hn hx hz hy
        by_cases hab : a = b
        · subst b
          rw [swap_last]
          exact with_shared_head a x y _ hn hx hy hz
        have hbc : b = c := by cases a <;> cases b <;> cases c <;> simp_all
        subst c
        rw [swap_first]
        exact with_shared_head b y z _ hn hy hz hx

end StarlikePalindromes

theorem OMA.solution : type_of% @OMA.S_arxiv_1805_10646.main := by
  intro n hn
  exact ⟨StarlikePalindromes.attainable n hn, fun _ _ _ hx hy hz => StarlikePalindromes.upper hn hx hy hz⟩

