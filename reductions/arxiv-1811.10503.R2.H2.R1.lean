import OMAReductions.R_arxiv_1811_10503_R2
import Mathlib

-- Reduction arxiv-1811.10503.R2.H2.R1 of the open step H2 of arxiv-1811.10503.R2 (Sun, Conjecture 4.1)
-- Credit: @ethduke
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-!
# H2 of arxiv-1811.10503.R2 reduces to one class, or a class of size at least 5

Setting of the target: `n ≥ 8`, `G` a finite commutative group with no element of order in
`[2, n+1]`, `A ⊆ G` with `|A| = n` fully blocked. The *class* of `x ∈ A` is the set of `y ∈ A` with
`zpowers y = zpowers x`. Two elements of `A` collide (`x ^ i = y ^ j`, `1 ≤ i, j ≤ n`) only inside
one class (`collide` of the parent file), so classes can be numbered independently.

Proved here (Theorem B, no blocking needed): if every class has at most 4 elements, `A` has a good
numbering. Exponents are dealt out class by class (smallest class first) from a pool `P ⊆ [1, n]`
containing `1`; a class `C` (order `m`) gets `E ⊆ P` with `|E| = |C|` and, for `|C| ≥ 2`, `E` not
`m`-symmetric (not closed under `e ↦ m - e`); a symmetric choice is repaired by one swap. A set
containing `1` is never symmetric. Size lemmas, for the table `T(u, e) = u ^ e` (distinct entries in
rows and columns):
* size 2: both bijections fail only if `a + b = m` (Lemma L: `e ≠ e'`, `e'^2 ≡ e^2 (mod m)` forces
  `e + e' = m`);
* size 3: every 3 x 3 array with distinct rows and columns has a rainbow transversal (kill counting:
  a symbol with `t` cells spoils at most `t / 2` transversals; checked by `decide` per symbol);
* size 4: same counting (`3 k(t) ≤ 4 t + 5 [t = 4]`) leaves only two symbols that fill every row; then
  `y = x ^ r` makes `e ↦ r e` a fixed-point-free permutation `ρ` of `E` modulo `m`, `ρ^2` or `ρ^4`
  fixes each `e`, and Lemma L makes `E` symmetric.

What remains (the two hypotheses):
* `H1`: `A` is a single class (one cyclic subgroup).
* `H2`: at least two classes, one of them with at least 5 elements.
-/

namespace OMA.R_arxiv_1811_10503_R2_H2_R1

def H1 : Prop := ∀ n : ℕ, 8 ≤ n → ∀ (G : Type) [CommGroup G] [Finite G],
  (∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) → ∀ A : Finset G, A.card = n →
  (∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ b ^ n = a ^ k) →
  (∀ a ∈ A, ∀ b ∈ A, Subgroup.zpowers a = Subgroup.zpowers b) →
  ∃ a : Fin n → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
    Function.Injective (fun i : Fin n => a i ^ (i.val + 1))

def H2 : Prop := ∀ n : ℕ, 8 ≤ n → ∀ (G : Type) [CommGroup G] [Finite G],
  (∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) → ∀ A : Finset G, A.card = n →
  (∀ b ∈ A, ∃ a ∈ A, a ≠ b ∧ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ b ^ n = a ^ k) →
  (∃ a ∈ A, ∃ b ∈ A, Subgroup.zpowers a ≠ Subgroup.zpowers b) →
  (∃ a ∈ A, ∃ B ⊆ A, 5 ≤ B.card ∧ ∀ b ∈ B, Subgroup.zpowers b = Subgroup.zpowers a) →
  ∃ a : Fin n → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
    Function.Injective (fun i : Fin n => a i ^ (i.val + 1))

/-! ## Arrays: kill counting for 3 x 3 and 4 x 4 tables -/

set_option maxHeartbeats 4000000 in
lemma k3 : ∀ p : Fin 3 → Option (Fin 3), (∀ i j, p i ≠ none → p i = p j → i = j) →
    2 * (Finset.univ.filter (fun σ : Fin 3 → Fin 3 => (∀ i j, σ i = σ j → i = j) ∧
      2 ≤ (Finset.univ.filter (fun i => p i = some (σ i))).card)).card ≤
      (Finset.univ.filter (fun i => p i ≠ none)).card := by
  decide +kernel

set_option maxHeartbeats 40000000 in
lemma k4 : ∀ p : Fin 4 → Option (Fin 4), (∀ i j, p i ≠ none → p i = p j → i = j) →
    3 * (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => (∀ i j, σ i = σ j → i = j) ∧
      2 ≤ (Finset.univ.filter (fun i => p i = some (σ i))).card)).card ≤
      4 * (Finset.univ.filter (fun i => p i ≠ none)).card +
      (if (Finset.univ.filter (fun i => p i ≠ none)).card = 4 then 5 else 0) := by
  decide +kernel

lemma perms3 : (Finset.univ.filter (fun σ : Fin 3 → Fin 3 => ∀ i j, σ i = σ j → i = j)).card = 6 := by
  decide +kernel

lemma perms4 : (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => ∀ i j, σ i = σ j → i = j)).card = 24 := by
  decide +kernel

lemma rho4 : ∀ ρ : Fin 4 → Fin 4, (∀ i j, ρ i = ρ j → i = j) → (∀ j, ρ j ≠ j) →
    ∀ j, ρ (ρ j) = j ∨ ρ (ρ (ρ (ρ j))) = j := by
  decide +kernel

/-- The counting frame for an `s × s` array with distinct entries in rows and columns
in which every transversal repeats a symbol. -/
lemma cnt {X : Type} [DecidableEq X] (s : ℕ) (T : Fin s → Fin s → X)
    (hrow : ∀ i j j', T i j = T i j' → j = j') (hcol : ∀ i i' j, T i j = T i' j → i = i')
    (hbad : ∀ σ : Fin s → Fin s, (∀ i j, σ i = σ j → i = j) →
      ∃ i j, T i (σ i) = T j (σ j) ∧ i ≠ j) :
    ∃ p : X → Fin s → Option (Fin s), (∀ x i j, p x i ≠ none → p x i = p x j → i = j) ∧
      (Finset.univ.filter (fun σ : Fin s → Fin s => ∀ i j, σ i = σ j → i = j)).card ≤
        ∑ x ∈ Finset.univ.image (fun c : Fin s × Fin s => T c.1 c.2),
          (Finset.univ.filter (fun σ : Fin s → Fin s => (∀ i j, σ i = σ j → i = j) ∧
            2 ≤ (Finset.univ.filter (fun i => p x i = some (σ i))).card)).card ∧
      ∑ x ∈ Finset.univ.image (fun c : Fin s × Fin s => T c.1 c.2),
          (Finset.univ.filter (fun i => p x i ≠ none)).card = s * s ∧
      ∀ x, (Finset.univ.filter (fun i => p x i ≠ none)).card = s → ∀ i, ∃ j, T i j = x := by
  classical
  let p : X → Fin s → Option (Fin s) := fun x i =>
    if h : ∃ j, T i j = x then some (Classical.choose h) else none
  have hp : ∀ x i j, p x i = some j ↔ T i j = x := by
    intro x i j
    constructor
    · intro h
      simp only [p] at h
      split_ifs at h with h'
      · rw [← Option.some_inj.mp h]
        exact Classical.choose_spec h'
    · intro h
      have h' : ∃ j, T i j = x := ⟨j, h⟩
      simp only [p, dif_pos h']
      congr 1
      exact hrow i _ _ ((Classical.choose_spec h').trans h.symm)
  have hpn : ∀ x i, p x i ≠ none ↔ ∃ j, T i j = x := by
    intro x i
    rw [Option.ne_none_iff_exists']
    simp only [hp]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro x i j hi hij
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hi
    have hj : p x j = some c := hij ▸ hc
    exact hcol i j c (((hp x i c).mp hc).trans ((hp x j c).mp hj).symm)
  · apply le_trans _ (Finset.card_biUnion_le)
    apply Finset.card_le_card
    intro σ hσ
    have hσ' := (Finset.mem_filter.mp hσ).2
    obtain ⟨i, j, hij, hne⟩ := hbad σ hσ'
    rw [Finset.mem_biUnion]
    refine ⟨T i (σ i), Finset.mem_image.mpr ⟨(i, σ i), Finset.mem_univ _, rfl⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hσ', ?_⟩
    have hsub : ({i, j} : Finset (Fin s)) ⊆
        Finset.univ.filter (fun k => p (T i (σ i)) k = some (σ k)) := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_filter, hp]
      rcases hk with rfl | rfl
      · exact ⟨Finset.mem_univ _, rfl⟩
      · exact ⟨Finset.mem_univ _, hij.symm⟩
    calc 2 = ({i, j} : Finset (Fin s)).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  · simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hrow' : ∀ i : Fin s, (∑ x ∈ Finset.univ.image (fun c : Fin s × Fin s => T c.1 c.2),
        if p x i ≠ none then 1 else 0) = s := by
      intro i
      rw [← Finset.card_filter]
      have heq : (Finset.univ.image (fun c : Fin s × Fin s => T c.1 c.2)).filter
          (fun x => p x i ≠ none) = Finset.univ.image (T i) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hpn]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · rintro ⟨j, hj⟩
          exact ⟨⟨(i, j), hj⟩, ⟨j, hj⟩⟩
      rw [heq, Finset.card_image_of_injective _ (fun j j' h => hrow i j j' h)]
      simp
    rw [Finset.sum_congr rfl (fun i _ => hrow' i)]
    simp
  · intro x hx i
    have huniv : Finset.univ.filter (fun i => p x i ≠ none) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hx]; simp)
    have hi : i ∈ Finset.univ.filter (fun i => p x i ≠ none) := by
      rw [huniv]
      exact Finset.mem_univ i
    exact (hpn x i).mp (Finset.mem_filter.mp hi).2

lemma arr3 {X : Type} [DecidableEq X] (T : Fin 3 → Fin 3 → X)
    (hrow : ∀ i j j', T i j = T i j' → j = j') (hcol : ∀ i i' j, T i j = T i' j → i = i') :
    ∃ σ : Fin 3 → Fin 3, (∀ i j, σ i = σ j → i = j) ∧
      ∀ i j, T i (σ i) = T j (σ j) → i = j := by
  by_contra hcon
  have hbad : ∀ σ : Fin 3 → Fin 3, (∀ i j, σ i = σ j → i = j) →
      ∃ i j, T i (σ i) = T j (σ j) ∧ i ≠ j := by
    intro σ hσ
    by_contra h
    push Not at h
    exact hcon ⟨σ, hσ, fun i j hij => h i j hij⟩
  obtain ⟨p, hpinj, h1, h2, -⟩ := cnt 3 T hrow hcol hbad
  rw [perms3] at h1
  have h3 : ∑ x ∈ Finset.univ.image (fun c : Fin 3 × Fin 3 => T c.1 c.2),
      2 * (Finset.univ.filter (fun σ : Fin 3 → Fin 3 => (∀ i j, σ i = σ j → i = j) ∧
            2 ≤ (Finset.univ.filter (fun i => p x i = some (σ i))).card)).card ≤
      ∑ x ∈ Finset.univ.image (fun c : Fin 3 × Fin 3 => T c.1 c.2),
          (Finset.univ.filter (fun i => p x i ≠ none)).card :=
    Finset.sum_le_sum (fun x _ => k3 (p x) (hpinj x))
  rw [← Finset.mul_sum, h2] at h3
  omega

lemma arr4 {X : Type} [DecidableEq X] (T : Fin 4 → Fin 4 → X)
    (hrow : ∀ i j j', T i j = T i j' → j = j') (hcol : ∀ i i' j, T i j = T i' j → i = i')
    (hbad : ∀ σ : Fin 4 → Fin 4, (∀ i j, σ i = σ j → i = j) →
      ∃ i j, T i (σ i) = T j (σ j) ∧ i ≠ j) :
    ∃ x y, x ≠ y ∧ (∀ i, ∃ j, T i j = x) ∧ (∀ i, ∃ j, T i j = y) := by
  obtain ⟨p, hpinj, h1, h2, h4⟩ := cnt 4 T hrow hcol hbad
  rw [perms4] at h1
  set S := Finset.univ.image (fun c : Fin 4 × Fin 4 => T c.1 c.2)
  have h3 : ∑ x ∈ S,
      3 * (Finset.univ.filter (fun σ : Fin 4 → Fin 4 => (∀ i j, σ i = σ j → i = j) ∧
            2 ≤ (Finset.univ.filter (fun i => p x i = some (σ i))).card)).card ≤
      ∑ x ∈ S, (4 * (Finset.univ.filter (fun i => p x i ≠ none)).card +
        (if (Finset.univ.filter (fun i => p x i ≠ none)).card = 4 then 5 else 0)) :=
    Finset.sum_le_sum (fun x _ => k4 (p x) (hpinj x))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_ite,
    Finset.sum_const_zero, Finset.sum_const, smul_eq_mul] at h3
  set F := S.filter (fun x => (Finset.univ.filter (fun i => p x i ≠ none)).card = 4)
  have hF : 1 < F.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hF
  exact ⟨x, y, hxy, h4 x (Finset.mem_filter.mp hx).2, h4 y (Finset.mem_filter.mp hy).2⟩

/-! ## Group side: one class at a time -/

/-- A nontrivial element has order at least `n + 2`. -/
lemma ord_ge {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {x : G} (hx : x ≠ 1) :
    n + 2 ≤ orderOf x := by
  have h0 := orderOf_pos x
  have h1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have h2 := hG x
  rw [Finset.mem_Icc] at h2
  omega

/-- Rows of the power table are injective. -/
lemma pow_inj_exp {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {x : G} (hx : x ≠ 1)
    {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : x ^ a = x ^ b) : a = b := by
  have hm := ord_ge hG hx
  have h' := pow_eq_pow_iff_modEq.mp h
  unfold Nat.ModEq at h'
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'

/-- Columns of the power table are injective. -/
lemma pow_inj_base {G : Type} [CommGroup G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {u v : G} {a : ℕ} (ha1 : 1 ≤ a)
    (ha : a ≤ n) (h : u ^ a = v ^ a) : u = v := by
  have h1 : (u / v) ^ a = 1 := by rw [div_pow, h, div_self']
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 := Nat.le_of_dvd (by omega) h2
  have h4 := orderOf_pos (u / v)
  have h5 := hG (u / v)
  rw [Finset.mem_Icc] at h5
  have h6 : orderOf (u / v) = 1 := by omega
  exact div_eq_one.mp (orderOf_eq_one_iff.mp h6)

lemma lemL_lt {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {g : G} (hg : g ≠ 1) {e e' : ℕ}
    (he : 1 ≤ e) (hlt : e < e') (hen' : e' ≤ n)
    (h : e' * e' ≡ e * e [MOD orderOf g]) : e + e' = orderOf g := by
  have hm := ord_ge hG hg
  have hle : e * e ≤ e' * e' := Nat.mul_self_le_mul_self hlt.le
  have hd : orderOf g ∣ e' * e' - e * e := (Nat.modEq_iff_dvd' hle).mp h.symm
  rw [Nat.mul_self_sub_mul_self_eq] at hd
  have hcop : (e' - e).Coprime (orderOf g) :=
    OMA.R_arxiv_1811_10503_R2.coprime_of_noSmall hG g (orderOf_pos g).ne' (by omega) (by omega)
  have hd2 : orderOf g ∣ e' + e := Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hd
  have := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd2 (by omega)
  omega

/-- Lemma L: two distinct exponents with equal squares modulo the order add up to the order. -/
lemma lemL {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {g : G} (hg : g ≠ 1) {e e' : ℕ}
    (he : 1 ≤ e) (hen : e ≤ n) (he' : 1 ≤ e') (hen' : e' ≤ n) (hne : e ≠ e')
    (h : e' * e' ≡ e * e [MOD orderOf g]) : e + e' = orderOf g := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact lemL_lt hG hg he hlt hen' h
  · have := lemL_lt hG hg he' hlt hen h.symm
    omega

lemma sq_step {m a b c : ℕ} (h1 : b ≡ a * c [MOD m]) (h2 : a ≡ b * c [MOD m]) :
    b * b ≡ a * a [MOD m] := by
  calc b * b ≡ a * c * b [MOD m] := h1.mul_right b
    _ = a * (b * c) := by ring
    _ ≡ a * a [MOD m] := h2.symm.mul_left a

lemma pair_good {G : Type} [Group G] [DecidableEq G] {u v : G} (huv : u ≠ v) {a b : ℕ} (hab : a ≠ b)
    (h : u ^ a ≠ v ^ b) :
    ∃ f : G → ℕ, (∀ c ∈ ({u, v} : Finset G), f c ∈ ({a, b} : Finset ℕ)) ∧
      Set.InjOn f (({u, v} : Finset G) : Set G) ∧
      Set.InjOn (fun c => c ^ f c) (({u, v} : Finset G) : Set G) := by
  classical
  have hvu : v ≠ u := huv.symm
  refine ⟨fun c => if c = u then a else b, ?_, ?_, ?_⟩
  · intro c hc
    by_cases hcu : c = u
    · simp [hcu]
    · simp [hcu]
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · simp [hvu] at hxy
      exact absurd hxy hab
    · simp [hvu] at hxy
      exact absurd hxy.symm hab
    · rfl
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · simp [hvu] at hxy
      exact absurd hxy h
    · simp [hvu] at hxy
      exact absurd hxy.symm h
    · rfl

/-- Size-2 classes (R2). -/
lemma good2 {G : Type} [CommGroup G] [Finite G] [DecidableEq G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) {u v : G} (huv : u ≠ v) (hu : u ≠ 1)
    {a b : ℕ} (hab : a ≠ b) (ha1 : 1 ≤ a) (ha : a ≤ n) (hb1 : 1 ≤ b) (hb : b ≤ n)
    (hsym : a + b ≠ orderOf u) :
    ∃ f : G → ℕ, (∀ c ∈ ({u, v} : Finset G), f c ∈ ({a, b} : Finset ℕ)) ∧
      Set.InjOn f (({u, v} : Finset G) : Set G) ∧
      Set.InjOn (fun c => c ^ f c) (({u, v} : Finset G) : Set G) := by
  by_cases h1 : u ^ a = v ^ b
  · by_cases h2 : u ^ b = v ^ a
    · exfalso
      have h3 : u ^ (a * a) = u ^ (b * b) := by
        calc u ^ (a * a) = (u ^ a) ^ a := pow_mul u a a
          _ = (v ^ b) ^ a := by rw [h1]
          _ = (v ^ a) ^ b := by rw [← pow_mul, ← pow_mul, mul_comm]
          _ = (u ^ b) ^ b := by rw [h2]
          _ = u ^ (b * b) := (pow_mul u b b).symm
      have h4 := pow_eq_pow_iff_modEq.mp h3
      have h5 := lemL hG hu hb1 hb ha1 ha (Ne.symm hab) h4
      exact hsym (by omega)
    · obtain ⟨f, h1', h2', h3'⟩ := pair_good huv (Ne.symm hab) h2
      refine ⟨f, fun c hc => ?_, h2', h3'⟩
      rw [Finset.pair_comm]
      exact h1' c hc
  · exact pair_good huv hab h1

/-- Enumerate a finset of size `s` by `Fin s`. -/
lemma enum {α : Type} (C : Finset α) {s : ℕ} (h : C.card = s) :
    ∃ u : Fin s → α, Function.Injective u ∧ (∀ i, u i ∈ C) ∧ ∀ c ∈ C, ∃ i, u i = c := by
  refine ⟨fun i => ((C.equivFinOfCardEq h).symm i : α), ?_, ?_, ?_⟩
  · intro i j hij
    exact (C.equivFinOfCardEq h).symm.injective (Subtype.val_injective hij)
  · intro i
    exact ((C.equivFinOfCardEq h).symm i).2
  · intro c hc
    exact ⟨C.equivFinOfCardEq h ⟨c, hc⟩, by simp⟩

/-- A rainbow transversal of the power table gives the exponents of a class. -/
lemma good_of_arr {G : Type} [Group G] {s : ℕ} (C : Finset G) (E : Finset ℕ) (u : Fin s → G)
    (hCu : ∀ c ∈ C, ∃ i, u i = c) (e : Fin s → ℕ)
    (heE : ∀ i, e i ∈ E) (he : Function.Injective e) (σ : Fin s → Fin s)
    (hσ : ∀ i j, σ i = σ j → i = j) (hT : ∀ i j, u i ^ e (σ i) = u j ^ e (σ j) → i = j) :
    ∃ f : G → ℕ, (∀ c ∈ C, f c ∈ E) ∧ Set.InjOn f C ∧ Set.InjOn (fun c => c ^ f c) C := by
  classical
  let f : G → ℕ := fun c => if h : ∃ i, u i = c then e (σ (Classical.choose h)) else 0
  have hf : ∀ c ∈ C, ∃ i, u i = c ∧ f c = e (σ i) := by
    intro c hc
    have h := hCu c hc
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp only [f, dif_pos h]⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨i, -, hi⟩ := hf c hc
    rw [hi]
    exact heE _
  · intro c hc c' hc' hcc
    obtain ⟨i, rfl, hi⟩ := hf c hc
    obtain ⟨i', rfl, hi'⟩ := hf c' hc'
    rw [hi, hi'] at hcc
    rw [hσ i i' (he hcc)]
  · intro c hc c' hc' hcc
    obtain ⟨i, rfl, hi⟩ := hf c hc
    obtain ⟨i', rfl, hi'⟩ := hf c' hc'
    simp only [hi, hi'] at hcc
    rw [hT i i' hcc]

/-- Two symbols filling every row of a 4 x 4 power table force the exponent set to be
symmetric: every exponent has a partner adding up to the order. -/
lemma sym4 {G : Type} [CommGroup G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) (u : Fin 4 → G) (e : Fin 4 → ℕ)
    (he1 : ∀ j, 1 ≤ e j) (hen : ∀ j, e j ≤ n) (heinj : Function.Injective e)
    (hu : Function.Injective u) (hu1 : ∀ i, u i ≠ 1)
    (hz : ∀ i, Subgroup.zpowers (u i) = Subgroup.zpowers (u 0))
    (x y : G) (hxy : x ≠ y) (hx : ∀ i, ∃ j, u i ^ e j = x) (hy : ∀ i, ∃ j, u i ^ e j = y) :
    ∀ j, ∃ j', e j + e j' = orderOf (u 0) := by
  have hrow : ∀ i j j', u i ^ e j = u i ^ e j' → j = j' := fun i j j' h =>
    heinj (pow_inj_exp hG (hu1 i) (hen j) (hen j') h)
  have hcol : ∀ i i' j, u i ^ e j = u i' ^ e j → i = i' := fun i i' j h =>
    hu (pow_inj_base hG (he1 j) (hen j) h)
  have hord : ∀ i, orderOf (u i) = orderOf (u 0) := by
    intro i
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, hz i]
  obtain ⟨j0, hj0⟩ := hx 0
  obtain ⟨j1, hj1⟩ := hy 0
  have hzx : Subgroup.zpowers x = Subgroup.zpowers (u 0) := by
    rw [← hj0]
    exact OMA.R_arxiv_1811_10503_R2.zpowers_pow_eq hG (u 0) (orderOf_pos _).ne' (he1 j0) (hen j0)
  have hyx : y ∈ Subgroup.zpowers x := by
    rw [hzx, ← hj1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨r, hr⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hyx)
  choose α hα using hx
  have hαinj : Function.Injective α := fun i i' h =>
    hcol i i' (α i) (by rw [hα i, h, hα i'])
  choose a ha using Finite.injective_iff_surjective.mp hαinj
  have hax : ∀ j, u (a j) ^ e j = x := fun j => by
    have := hα (a j)
    rwa [ha j] at this
  choose β hβ using hy
  have hρinj : ∀ j j', β (a j) = β (a j') → j = j' := by
    intro j j' h
    have h1 : a j = a j' := hcol (a j) (a j') (β (a j)) (by rw [hβ (a j), h, hβ (a j')])
    exact hrow (a j) j j' (by rw [hax j, h1, hax j'])
  have hρfp : ∀ j, β (a j) ≠ j := by
    intro j h
    apply hxy
    rw [← hax j, ← hβ (a j), h]
  have hρmod : ∀ j, e (β (a j)) ≡ e j * r [MOD orderOf (u 0)] := by
    intro j
    rw [← hord (a j)]
    apply pow_eq_pow_iff_modEq.mp
    rw [hβ (a j), pow_mul, hax j, hr]
  have hA : ∀ k, e (β (a (β (a k)))) ≡ e k * (r * r) [MOD orderOf (u 0)] := by
    intro k
    calc e (β (a (β (a k)))) ≡ e (β (a k)) * r [MOD orderOf (u 0)] := hρmod (β (a k))
      _ ≡ e k * r * r [MOD orderOf (u 0)] := (hρmod k).mul_right r
      _ = e k * (r * r) := by ring
  intro j
  by_cases h2 : β (a (β (a j))) = j
  · refine ⟨β (a j), ?_⟩
    have hne : e j ≠ e (β (a j)) := fun h => hρfp j (heinj h).symm
    apply lemL hG (hu1 0) (he1 j) (hen j) (he1 _) (hen _) hne
    apply sq_step (hρmod j)
    have := hρmod (β (a j))
    rwa [h2] at this
  · rcases rho4 (fun k => β (a k)) hρinj hρfp j with h2' | h4
    · exact absurd h2' h2
    · refine ⟨β (a (β (a j))), ?_⟩
      have hne : e j ≠ e (β (a (β (a j)))) := fun h => h2 (heinj h).symm
      apply lemL hG (hu1 0) (he1 j) (hen j) (he1 _) (hen _) hne
      apply sq_step (hA j)
      have := hA (β (a (β (a j))))
      rwa [h4] at this

/-- The elements of a class with at least two elements are nontrivial. -/
lemma ne_one_of_class {G : Type} [Group G] (C : Finset G) (x0 : G)
    (hC : ∀ c ∈ C, Subgroup.zpowers c = Subgroup.zpowers x0) (h2 : 2 ≤ C.card) :
    ∀ c ∈ C, c ≠ 1 := by
  classical
  intro c hc hc1
  have hsub : C ⊆ {1} := by
    intro c' hc'
    rw [Finset.mem_singleton]
    have : Subgroup.zpowers c' = ⊥ := by
      rw [hC c' hc', ← hC c hc, hc1, Subgroup.zpowers_one_eq_bot]
    exact Subgroup.zpowers_eq_bot.mp this
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

/-- The size lemmas: a class of size at most 4 and a non-symmetric exponent set. -/
lemma classGood {G : Type} [CommGroup G] [Finite G] {n : ℕ}
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) (C : Finset G) (x0 : G)
    (hx0 : x0 ∈ C) (hC : ∀ c ∈ C, Subgroup.zpowers c = Subgroup.zpowers x0) (hs : C.card ≤ 4)
    (E : Finset ℕ) (hE : ∀ e ∈ E, 1 ≤ e ∧ e ≤ n) (hEc : E.card = C.card)
    (hsym : 2 ≤ C.card → ¬ ∀ e ∈ E, orderOf x0 - e ∈ E) :
    ∃ f : G → ℕ, (∀ c ∈ C, f c ∈ E) ∧ Set.InjOn f C ∧ Set.InjOn (fun c => c ^ f c) C := by
  classical
  have hord : ∀ c ∈ C, orderOf c = orderOf x0 := fun c hc => by
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, hC c hc]
  have hne1 := ne_one_of_class C x0 hC
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨x0, hx0⟩
  have hcases : C.card = 1 ∨ C.card = 2 ∨ C.card = 3 ∨ C.card = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hEc.trans h1)
    refine ⟨fun _ => a, ?_, ?_, ?_⟩
    · intro c' _
      exact Finset.mem_singleton_self a
    · intro x hx y hy _
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
    · intro x hx y hy _
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hEc.trans h2)
    have hu : u ≠ 1 := hne1 (by omega) u (by simp)
    have hsym' : a + b ≠ orderOf u := by
      intro hsum
      apply hsym (by omega)
      rw [← hord u (by simp)]
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
      rcases he with rfl | rfl
      · right
        omega
      · left
        omega
    exact good2 hG huv hu hab (hE a (by simp)).1 (hE a (by simp)).2 (hE b (by simp)).1
      (hE b (by simp)).2 hsym'
  · obtain ⟨u, hu, huC, hCu⟩ := enum C h3
    obtain ⟨e, he, heE, hEe⟩ := enum E (hEc.trans h3)
    have hu1 : ∀ i, u i ≠ 1 := fun i => hne1 (by omega) _ (huC i)
    obtain ⟨σ, hσ, hT⟩ := arr3 (fun i j => u i ^ e j)
      (fun i j j' h => he (pow_inj_exp hG (hu1 i) (hE _ (heE j)).2 (hE _ (heE j')).2 h))
      (fun i i' j h => hu (pow_inj_base hG (hE _ (heE j)).1 (hE _ (heE j)).2 h))
    exact good_of_arr C E u hCu e heE he σ hσ hT
  · obtain ⟨u, hu, huC, hCu⟩ := enum C h4
    obtain ⟨e, he, heE, hEe⟩ := enum E (hEc.trans h4)
    have hu1 : ∀ i, u i ≠ 1 := fun i => hne1 (by omega) _ (huC i)
    have hrow : ∀ i j j', u i ^ e j = u i ^ e j' → j = j' := fun i j j' h =>
      he (pow_inj_exp hG (hu1 i) (hE _ (heE j)).2 (hE _ (heE j')).2 h)
    have hcol : ∀ i i' j, u i ^ e j = u i' ^ e j → i = i' := fun i i' j h =>
      hu (pow_inj_base hG (hE _ (heE j)).1 (hE _ (heE j)).2 h)
    by_cases hgood : ∃ σ : Fin 4 → Fin 4, (∀ i j, σ i = σ j → i = j) ∧
        ∀ i j, u i ^ e (σ i) = u j ^ e (σ j) → i = j
    · obtain ⟨σ, hσ, hT⟩ := hgood
      exact good_of_arr C E u hCu e heE he σ hσ hT
    · exfalso
      have hbad : ∀ σ : Fin 4 → Fin 4, (∀ i j, σ i = σ j → i = j) →
          ∃ i j, u i ^ e (σ i) = u j ^ e (σ j) ∧ i ≠ j := by
        intro σ hσ
        by_contra h
        push Not at h
        exact hgood ⟨σ, hσ, fun i j hij => h i j hij⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := arr4 (fun i j => u i ^ e j) hrow hcol hbad
      have hz : ∀ i, Subgroup.zpowers (u i) = Subgroup.zpowers (u 0) := fun i => by
        rw [hC _ (huC i), hC _ (huC 0)]
      have hsy := sym4 hG u e (fun j => (hE _ (heE j)).1) (fun j => (hE _ (heE j)).2) he hu hu1
        hz x y hxy hx hy
      apply hsym (by omega)
      intro a ha
      obtain ⟨j, rfl⟩ := hEe a ha
      obtain ⟨j', hj'⟩ := hsy j
      rw [← hord (u 0) (huC 0), ← hj', Nat.add_sub_cancel_left]
      exact heE j'

/-! ## Theorem B: the induction over classes -/

/-- Choosing a non-symmetric exponent set from a pool, with one swap if needed. -/
lemma chooseE (Q : Finset ℕ) (s m : ℕ) (hsQ : s ≤ Q.card)
    (h2 : 2 ≤ s → s + 1 ≤ Q.card ∧ ¬ 2 ∣ m ∧ ∀ q ∈ Q, q ≤ m) :
    ∃ E ⊆ Q, E.card = s ∧ (2 ≤ s → ¬ ∀ e ∈ E, m - e ∈ E) := by
  classical
  obtain ⟨E0, hE0Q, hE0c⟩ := Finset.exists_subset_card_eq hsQ
  by_cases hs : 2 ≤ s
  swap
  · exact ⟨E0, hE0Q, hE0c, fun h => absurd h hs⟩
  by_cases hsym : ∀ e ∈ E0, m - e ∈ E0
  swap
  · exact ⟨E0, hE0Q, hE0c, fun _ => hsym⟩
  obtain ⟨hQc, hodd, hQm⟩ := h2 hs
  obtain ⟨a, ha⟩ : E0.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ : (Q \ E0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hE0Q]
    omega
  rw [Finset.mem_sdiff] at hb
  refine ⟨insert b (E0.erase a), ?_, ?_, fun _ => ?_⟩
  · intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hb.1
    · exact hE0Q (Finset.mem_of_mem_erase hx)
  · rw [Finset.card_insert_of_notMem (fun h => hb.2 (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem ha]
    omega
  · intro hsym2
    have hma : m - a ∈ E0 := hsym a ha
    have ham : a ≤ m := hQm a (hE0Q ha)
    have hne : m - a ≠ a := by omega
    have h1 : m - a ∈ insert b (E0.erase a) :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hma⟩)
    have h2' := hsym2 (m - a) h1
    rw [show m - (m - a) = a by omega, Finset.mem_insert, Finset.mem_erase] at h2'
    rcases h2' with h | h
    · exact hb.2 (h ▸ ha)
    · exact h.1 rfl

/-- Theorem B (R4), with an arbitrary pool `P` of exponents containing `1`. -/
lemma thmB {G : Type} [CommGroup G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hG : ∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) :
    ∀ A : Finset G, (∀ x ∈ A, ∀ B ⊆ A,
      (∀ b ∈ B, Subgroup.zpowers b = Subgroup.zpowers x) → B.card ≤ 4) →
    ∀ P : Finset ℕ, (∀ p ∈ P, 1 ≤ p ∧ p ≤ n) → P.card = A.card → (A.Nonempty → 1 ∈ P) →
    ∃ f : G → ℕ, (∀ x ∈ A, f x ∈ P) ∧ Set.InjOn f A ∧ Set.InjOn (fun x => x ^ f x) A := by
  classical
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
  intro hcls P hP hPc h1P
  rcases A.eq_empty_or_nonempty with hA | hne
  · subst hA
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      simp at hx
    · simp
    · simp
  obtain ⟨x0, hx0, hmin⟩ := A.exists_min_image
    (fun x => (A.filter (fun y => Subgroup.zpowers y = Subgroup.zpowers x)).card) hne
  set C := A.filter (fun y => Subgroup.zpowers y = Subgroup.zpowers x0) with hCdef
  have hCA : C ⊆ A := Finset.filter_subset _ _
  have hx0C : x0 ∈ C := Finset.mem_filter.mpr ⟨hx0, rfl⟩
  have hCcls : ∀ c ∈ C, Subgroup.zpowers c = Subgroup.zpowers x0 := fun c hc =>
    (Finset.mem_filter.mp hc).2
  have hs4 : C.card ≤ 4 := hcls x0 hx0 C hCA hCcls
  have h2s : 2 ≤ C.card → n + 2 ≤ orderOf x0 ∧ ¬ 2 ∣ orderOf x0 := by
    intro h2
    have hx01 : x0 ≠ 1 := ne_one_of_class C x0 hCcls h2 x0 hx0C
    refine ⟨ord_ge hG hx01, ?_⟩
    have hcop := OMA.R_arxiv_1811_10503_R2.coprime_of_noSmall hG x0 (orderOf_pos x0).ne'
      (r := 2) (by omega) hn
    intro hd
    have := Nat.Coprime.eq_one_of_dvd hcop hd
    omega
  have h1P' : 1 ∈ P := h1P hne
  by_cases hAC : A ⊆ C
  · have hCeq : C = A := Finset.Subset.antisymm hCA hAC
    have hsym : 2 ≤ C.card → ¬ ∀ e ∈ P, orderOf x0 - e ∈ P := by
      intro h2 hall
      have h1 := hall 1 h1P'
      have := (hP _ h1).2
      have := (h2s h2).1
      omega
    obtain ⟨f, hf1, hf2, hf3⟩ := classGood hG C x0 hx0C hCcls hs4 P hP (by rw [hPc, hCeq]) hsym
    rw [hCeq] at hf1 hf2 hf3
    exact ⟨f, hf1, hf2, hf3⟩
  · obtain ⟨y, hyA, hyC⟩ := Finset.not_subset.mp hAC
    have hCy : (A.filter (fun z => Subgroup.zpowers z = Subgroup.zpowers y)) ⊆ A \ C := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [Finset.mem_sdiff]
      refine ⟨hz.1, fun hzC => hyC ?_⟩
      exact Finset.mem_filter.mpr ⟨hyA, by rw [← hz.2, hCcls z hzC]⟩
    have hmy := hmin y hyA
    have hcardy := Finset.card_le_card hCy
    have hA'c : (A \ C).card + C.card = A.card := Finset.card_sdiff_add_card_eq_card hCA
    have hQc : (P.erase 1).card + 1 = P.card := Finset.card_erase_add_one h1P'
    obtain ⟨E, hEQ, hEc, hEsym⟩ := chooseE (P.erase 1) C.card (orderOf x0) (by omega)
      (fun h2 => ⟨by omega, (h2s h2).2, fun q hq => by
        have := (hP q (Finset.mem_of_mem_erase hq)).2
        have := (h2s h2).1
        omega⟩)
    have hEP : E ⊆ P := fun e he => Finset.mem_of_mem_erase (hEQ he)
    obtain ⟨f1, hf1E, hf1inj, hf1pow⟩ :=
      classGood hG C x0 hx0C hCcls hs4 E (fun e he => hP e (hEP he)) hEc hEsym
    have hA'A : A \ C ⊂ A := Finset.sdiff_ssubset hCA ⟨x0, hx0C⟩
    obtain ⟨f2, hf2P, hf2inj, hf2pow⟩ := ih (A \ C) hA'A
      (fun x hx B hB hBx => hcls x (Finset.sdiff_subset hx) B (hB.trans Finset.sdiff_subset) hBx)
      (P \ E) (fun p hp => hP p (Finset.sdiff_subset hp))
      (by rw [Finset.card_sdiff_of_subset hEP]; omega)
      (fun _ => Finset.mem_sdiff.mpr ⟨h1P', fun h => (Finset.mem_erase.mp (hEQ h)).1 rfl⟩)
    have hmemA' : ∀ z ∈ A, z ∉ C → z ∈ A \ C := fun z hz hzC => Finset.mem_sdiff.mpr ⟨hz, hzC⟩
    refine ⟨fun z => if z ∈ C then f1 z else f2 z, ?_, ?_, ?_⟩
    · intro z hz
      dsimp only
      by_cases hzC : z ∈ C
      · rw [if_pos hzC]
        exact hEP (hf1E z hzC)
      · rw [if_neg hzC]
        exact Finset.sdiff_subset (hf2P z (hmemA' z hz hzC))
    · intro z hz w hw hzw
      dsimp only at hzw
      by_cases hzC : z ∈ C <;> by_cases hwC : w ∈ C
      · rw [if_pos hzC, if_pos hwC] at hzw
        exact hf1inj hzC hwC hzw
      · rw [if_pos hzC, if_neg hwC] at hzw
        exfalso
        have h1 := hf1E z hzC
        have h2 := hf2P w (hmemA' w hw hwC)
        rw [← hzw] at h2
        exact (Finset.mem_sdiff.mp h2).2 h1
      · rw [if_neg hzC, if_pos hwC] at hzw
        exfalso
        have h1 := hf1E w hwC
        have h2 := hf2P z (hmemA' z hz hzC)
        rw [hzw] at h2
        exact (Finset.mem_sdiff.mp h2).2 h1
      · rw [if_neg hzC, if_neg hwC] at hzw
        exact hf2inj (hmemA' z hz hzC) (hmemA' w hw hwC) hzw
    · intro z hz w hw hzw
      dsimp only at hzw
      by_cases hzC : z ∈ C <;> by_cases hwC : w ∈ C
      · rw [if_pos hzC, if_pos hwC] at hzw
        exact hf1pow hzC hwC hzw
      · rw [if_pos hzC, if_neg hwC] at hzw
        exfalso
        have he1 := hP _ (hEP (hf1E z hzC))
        have he2 := hP _ (Finset.sdiff_subset (hf2P w (hmemA' w hw hwC)))
        have hcz := OMA.R_arxiv_1811_10503_R2.collide hG (orderOf_pos z).ne' (orderOf_pos w).ne'
          he1.1 he1.2 he2.1 he2.2 hzw
        exact hwC (Finset.mem_filter.mpr ⟨hw, by rw [← hcz, hCcls z hzC]⟩)
      · rw [if_neg hzC, if_pos hwC] at hzw
        exfalso
        have he1 := hP _ (hEP (hf1E w hwC))
        have he2 := hP _ (Finset.sdiff_subset (hf2P z (hmemA' z hz hzC)))
        have hcz := OMA.R_arxiv_1811_10503_R2.collide hG (orderOf_pos w).ne' (orderOf_pos z).ne'
          he1.1 he1.2 he2.1 he2.2 hzw.symm
        exact hzC (Finset.mem_filter.mpr ⟨hz, by rw [← hcz, hCcls w hwC]⟩)
      · rw [if_neg hzC, if_neg hwC] at hzw
        exact hf2pow (hmemA' z hz hzC) (hmemA' w hw hwC) hzw

/-- A bijection from `A` onto `[1, n]` gives the numbering. -/
lemma toFin {G : Type} [Group G] (A : Finset G) (n : ℕ) (hA : A.card = n) (f : G → ℕ)
    (hfP : ∀ x ∈ A, f x ∈ Finset.Icc 1 n) (hinj : Set.InjOn f A)
    (hpow : Set.InjOn (fun x => x ^ f x) A) :
    ∃ a : Fin n → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
      Function.Injective (fun i : Fin n => a i ^ (i.val + 1)) := by
  classical
  have him : A.image f = Finset.Icc 1 n := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      exact hfP x hx
    · rw [Finset.card_image_of_injOn hinj, hA]
      simp
  have hex : ∀ i : Fin n, ∃ x ∈ A, f x = i.val + 1 := by
    intro i
    have : i.val + 1 ∈ A.image f := by
      rw [him, Finset.mem_Icc]
      omega
    exact Finset.mem_image.mp this
  choose a ha hfa using hex
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have := hfa i
    rw [hij, hfa j] at this
    omega
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ha i
    · intro hx
      have hfx := Finset.mem_Icc.mp (hfP x hx)
      refine ⟨⟨f x - 1, by omega⟩, ?_⟩
      apply hinj (ha _) hx
      rw [hfa]
      dsimp only
      omega
  · intro i j hij
    dsimp only at hij
    have h1 : a i ^ f (a i) = a j ^ f (a j) := by
      rw [hfa i, hfa j]
      exact hij
    have h2 := hpow (ha i) (ha j) h1
    apply Fin.ext
    have := hfa i
    rw [h2, hfa j] at this
    omega

theorem main : H1 → H2 → OMA.R_arxiv_1811_10503_R2.H2 := by
  intro h1 h2 n hn G _ _ hG A hA hblock
  classical
  by_cases hone : ∀ a ∈ A, ∀ b ∈ A, Subgroup.zpowers a = Subgroup.zpowers b
  · exact h1 n hn G hG A hA hblock hone
  have hone' : ∃ a ∈ A, ∃ b ∈ A, Subgroup.zpowers a ≠ Subgroup.zpowers b := by
    by_contra hc
    push Not at hc
    exact hone hc
  by_cases hbig : ∃ a ∈ A, ∃ B ⊆ A, 5 ≤ B.card ∧
      ∀ b ∈ B, Subgroup.zpowers b = Subgroup.zpowers a
  · exact h2 n hn G hG A hA hblock hone' hbig
  have hcls : ∀ x ∈ A, ∀ B ⊆ A,
      (∀ b ∈ B, Subgroup.zpowers b = Subgroup.zpowers x) → B.card ≤ 4 := by
    intro x hx B hB hBx
    by_contra hc
    exact hbig ⟨x, hx, B, hB, by omega, hBx⟩
  obtain ⟨f, hfP, hfinj, hfpow⟩ := thmB (by omega) hG A hcls (Finset.Icc 1 n)
    (fun p hp => Finset.mem_Icc.mp hp) (by simp [hA]) (fun _ => by
      rw [Finset.mem_Icc]
      omega)
  exact toFin A n hA f hfP hfinj hfpow

end OMA.R_arxiv_1811_10503_R2_H2_R1
