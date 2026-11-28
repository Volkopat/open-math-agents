import OMAStatements.S_arxiv_1804_10476

/-!
Disproof of the conjecture of Henning, Mohr and Rautenbach (arXiv:1804.10476) on the number of
minimum total dominating sets of trees.

Counterexample (not ours): J. Petr, J. Portier and L. Versteegen, On the number of minimum
dominating sets and total dominating sets in forests, arXiv:2206.13182, Lemmas 4.1 and 4.2: the
tree `G(k, l, m)` with `k = m = 3`, `l = 16`. It has a root `y` with children `x a` (`a < 3`),
each `x a` has children `w a b` (`b < 16`), each `w a b` has one child `v a b`, and each `v a b`
has three leaves `u a b c`. So `n = 244`, `γ_t = 97` and the tree has
`3 · (4 ^ 16 - 3 ^ 16) ^ 3 ≈ 2.306 · 10 ^ 29` minimum total dominating sets, while the conjectured
bound is `(391 / 97) ^ (97 / 2) ≈ 2.302 · 10 ^ 29`.
-/

open OMA.S_arxiv_1804_10476

namespace OMADisproofAux

/-- The vertices of `G(3, 16, 3)`. -/
inductive Vx
  | y
  | x (a : Fin 3)
  | w (a : Fin 3) (b : Fin 16)
  | v (a : Fin 3) (b : Fin 16)
  | u (a : Fin 3) (b : Fin 16) (c : Fin 3)
  deriving DecidableEq, Fintype

open Vx

/-- The parent of a vertex (the root is its own parent). -/
def par : Vx → Vx
  | y => y
  | x _ => y
  | w a _ => x a
  | v a b => w a b
  | u a b _ => v a b

/-- The depth of a vertex. -/
def rk : Vx → ℕ
  | y => 0
  | x _ => 1
  | w _ _ => 2
  | v _ _ => 3
  | u _ _ _ => 4

theorem rk_par (p : Vx) (hp : p ≠ y) : rk (par p) < rk p := by
  cases p <;> simp_all [par, rk]

theorem par_ne (p : Vx) (hp : p ≠ y) : par p ≠ p := by
  intro h; have := rk_par p hp; rw [h] at this; exact lt_irrefl _ this

/-- The tree `G(3, 16, 3)`: every vertex other than the root is joined to its parent. -/
def T : SimpleGraph Vx where
  Adj p q := (p ≠ y ∧ par p = q) ∨ (q ≠ y ∧ par q = p)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨hp, h⟩ | ⟨hp, h⟩ <;> exact par_ne p hp h⟩

instance : DecidableRel T.Adj := fun p q =>
  inferInstanceAs (Decidable ((p ≠ y ∧ par p = q) ∨ (q ≠ y ∧ par q = p)))

set_option maxRecDepth 100000 in
theorem card_Vx : Fintype.card Vx = 244 := by decide

/-- A vertex is adjacent to its parent. -/
theorem adj_par (p : Vx) (hp : p ≠ y) : T.Adj (par p) p := by
  show (par p ≠ y ∧ par (par p) = p) ∨ (p ≠ y ∧ par p = par p)
  exact Or.inr ⟨hp, rfl⟩

theorem adj_par' (p : Vx) (hp : p ≠ y) : T.Adj p (par p) := (adj_par p hp).symm

/-! ### `T` is a tree -/

theorem reach_root (p : Vx) : T.Reachable y p := by
  have hx : ∀ a, T.Reachable y (x a) := fun a => (adj_par (x a) (by simp)).reachable
  have hw : ∀ a b, T.Reachable y (w a b) := fun a b =>
    (hx a).trans (adj_par (w a b) (by simp)).reachable
  have hv : ∀ a b, T.Reachable y (v a b) := fun a b =>
    (hw a b).trans (adj_par (v a b) (by simp)).reachable
  cases p with
  | y => exact SimpleGraph.Reachable.refl _
  | x a => exact hx a
  | w a b => exact hw a b
  | v a b => exact hv a b
  | u a b c => exact (hv a b).trans (adj_par (u a b c) (by simp)).reachable

theorem T_connected : T.Connected := by
  have : Nonempty Vx := ⟨y⟩
  exact SimpleGraph.Connected.mk (fun p q => (reach_root p).symm.trans (reach_root q))

/-- Every edge is `s(p, par p)` for exactly one non-root vertex `p`. -/
def edgeOf (p : {p : Vx // p ≠ y}) : T.edgeSet :=
  ⟨s(p.1, par p.1), Or.inl ⟨p.2, rfl⟩⟩

theorem edgeOf_bij : Function.Bijective edgeOf := by
  constructor
  · rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h1
    · dsimp only at h1 h2
      have a := rk_par p hp
      have b := rk_par q hq
      rw [h2] at a; rw [← h1] at b
      omega
  · rintro ⟨e, he⟩
    revert he
    refine Sym2.ind (fun p q => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeSet] at he
    rcases he with ⟨hp, rfl⟩ | ⟨hq, rfl⟩
    · exact ⟨⟨p, hp⟩, rfl⟩
    · exact ⟨⟨q, hq⟩, Subtype.ext Sym2.eq_swap⟩

theorem T_isTree : T.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨T_connected, ?_⟩
  have h243 : Fintype.card {p : Vx // p ≠ y} = 243 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_Vx]
  rw [← Nat.card_congr (Equiv.ofBijective _ edgeOf_bij), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, h243, card_Vx]

/-! ### Total dominating sets -/

theorem adj_u (a b c) (q : Vx) : T.Adj (u a b c) q ↔ q = v a b := by
  cases q <;> simp [T, par] <;>
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

theorem adj_y (q : Vx) : T.Adj y q ↔ ∃ a, q = x a := by
  cases q <;> simp [T, par]

theorem adj_v (a b) (q : Vx) : T.Adj (v a b) q ↔ q = w a b ∨ ∃ c, q = u a b c := by
  cases q <;> simp [T, par, eq_comm, and_comm]

/-- The vertex `nb a b c` adjacent to `v a b`: `w a b` for `c = 0`, a leaf `u a b (c - 1)`
otherwise. -/
def nb (a : Fin 3) (b : Fin 16) : Fin 4 → Vx
  | 0 => w a b
  | 1 => u a b 0
  | 2 => u a b 1
  | 3 => u a b 2

theorem adj_nb (a b c) : T.Adj (v a b) (nb a b c) := by
  rw [adj_v]; fin_cases c <;> simp [nb]

theorem nb_inj (a b) : Function.Injective (nb a b) := by
  intro c c' h; fin_cases c <;> fin_cases c' <;> simp_all [nb]

theorem nb_row {a a' b b' c c'} (h : nb a b c = nb a' b' c') : a = a' ∧ b = b' := by
  fin_cases c <;> fin_cases c' <;> simp_all [nb]

theorem nb_ne_v (a b c a' b') : nb a b c ≠ v a' b' := by fin_cases c <;> simp [nb]
theorem nb_ne_x (a b c a') : nb a b c ≠ x a' := by fin_cases c <;> simp [nb]

/-- Every vertex `v a b` is adjacent to `nb a b c` for some `c`, and only to those. -/
theorem adj_v_nb (a b) (q : Vx) (h : T.Adj (v a b) q) : ∃ c, q = nb a b c := by
  rw [adj_v] at h
  rcases h with rfl | ⟨c, rfl⟩
  · exact ⟨0, rfl⟩
  · fin_cases c
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- A lower bound: every total dominating set has at least 97 vertices. -/
theorem card_ge (D : Finset Vx) (hD : IsTotalDominating T D) : 97 ≤ D.card := by
  classical
  have hv : ∀ a b, v a b ∈ D := by
    intro a b
    obtain ⟨q, hq, hadj⟩ := hD (u a b 0)
    rw [adj_u] at hadj; exact hadj ▸ hq
  have hy : ∃ a, x a ∈ D := by
    obtain ⟨q, hq, hadj⟩ := hD y
    rw [adj_y] at hadj; obtain ⟨a, rfl⟩ := hadj; exact ⟨a, hq⟩
  have hn : ∀ p : Fin 3 × Fin 16, ∃ c, nb p.1 p.2 c ∈ D := by
    rintro ⟨a, b⟩
    obtain ⟨q, hq, hadj⟩ := hD (v a b)
    obtain ⟨c, rfl⟩ := adj_v_nb a b q hadj
    exact ⟨c, hq⟩
  choose g hg using hn
  obtain ⟨a0, ha0⟩ := hy
  let S1 : Finset Vx := Finset.univ.image (fun p : Fin 3 × Fin 16 => v p.1 p.2)
  let S3 : Finset Vx := Finset.univ.image (fun p : Fin 3 × Fin 16 => nb p.1 p.2 (g p))
  have c1 : S1.card = 48 := by
    rw [Finset.card_image_of_injective]
    · simp
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h; simp_all
  have c3 : S3.card = 48 := by
    rw [Finset.card_image_of_injective]
    · simp
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      obtain ⟨rfl, rfl⟩ := nb_row h; rfl
  have d13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro q h1 h3
    simp only [S1, S3, Finset.mem_image, Finset.mem_univ, true_and] at h1 h3
    obtain ⟨p, rfl⟩ := h1; obtain ⟨p', hp'⟩ := h3
    exact nb_ne_v _ _ _ _ _ hp'
  have dx : x a0 ∉ S1 ∪ S3 := by
    simp only [S1, S3, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hp⟩; cases hp
    · rintro ⟨p, hp⟩; exact nb_ne_x _ _ _ _ hp
  have hsub : insert (x a0) (S1 ∪ S3) ⊆ D := by
    intro q hq
    simp only [S1, S3, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hq
    rcases hq with rfl | ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact ha0
    · exact hv p.1 p.2
    · exact hg p
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem dx, Finset.card_union_of_disjoint d13, c1, c3] at this
  omega

/-! ### The family of minimum total dominating sets -/

/-- The choices of a neighbour of each `v a b` such that each `x a` is dominated. -/
abbrev Good : Type := {f : Fin 16 → Fin 4 // ∃ b, f b = 0}

theorem card_exists_eq (n k : ℕ) (c : Fin k) :
    Fintype.card {f : Fin n → Fin k // ∃ b, f b = c} = k ^ n - (k - 1) ^ n := by
  have hne : Fintype.card {d : Fin k // ¬ d = c} = k - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have e : {f : Fin n → Fin k // ¬ ∃ b, f b = c} ≃ (Fin n → {d : Fin k // ¬ d = c}) :=
    { toFun := fun f b => ⟨f.1 b, fun h => f.2 ⟨b, h⟩⟩
      invFun := fun g => ⟨fun b => (g b).1, fun ⟨b, hb⟩ => (g b).2 hb⟩
      left_inv := fun f => rfl
      right_inv := fun g => rfl }
  have h1 : Fintype.card {f : Fin n → Fin k // ¬ ∃ b, f b = c} = (k - 1) ^ n := by
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, hne]
  have h2 := Fintype.card_subtype_compl (fun f : Fin n → Fin k => ∃ b, f b = c)
  have h3 := Fintype.card_subtype_le (fun f : Fin n → Fin k => ∃ b, f b = c)
  rw [h1, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h2
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h3
  generalize k ^ n = A at *
  generalize (k - 1) ^ n = B at *
  omega

theorem card_Good : Fintype.card Good = 4 ^ 16 - 3 ^ 16 :=
  card_exists_eq 16 4 0

/-- The minimum total dominating set given by `i` and the choices `F`. -/
def Phi (q : Fin 3 × (Fin 3 → Good)) : Finset Vx :=
  insert (x q.1) (Finset.univ.image (fun p : Fin 3 × Fin 16 => v p.1 p.2) ∪
    Finset.univ.image (fun p : Fin 3 × Fin 16 => nb p.1 p.2 ((q.2 p.1).1 p.2)))

theorem mem_Phi (q : Fin 3 × (Fin 3 → Good)) (r : Vx) :
    r ∈ Phi q ↔ r = x q.1 ∨ (∃ a b, r = v a b) ∨ ∃ a b, r = nb a b ((q.2 a).1 b) := by
  simp only [Phi, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro (h | ⟨a, b, h⟩ | ⟨a, b, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, b, h.symm⟩)
    · exact Or.inr (Or.inr ⟨a, b, h.symm⟩)
  · rintro (h | ⟨a, b, h⟩ | ⟨a, b, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, b, h.symm⟩)
    · exact Or.inr (Or.inr ⟨a, b, h.symm⟩)

theorem Phi_tds (q : Fin 3 × (Fin 3 → Good)) : IsTotalDominating T (Phi q) := by
  intro r
  cases r with
  | y => exact ⟨x q.1, (mem_Phi _ _).2 (Or.inl rfl), adj_par (x q.1) (by simp)⟩
  | x a =>
    obtain ⟨b, hb⟩ := (q.2 a).2
    refine ⟨w a b, (mem_Phi _ _).2 (Or.inr (Or.inr ⟨a, b, by rw [hb]; rfl⟩)), adj_par (w a b) (by simp)⟩
  | w a b => exact ⟨v a b, (mem_Phi _ _).2 (Or.inr (Or.inl ⟨a, b, rfl⟩)), adj_par (v a b) (by simp)⟩
  | v a b => exact ⟨_, (mem_Phi _ _).2 (Or.inr (Or.inr ⟨a, b, rfl⟩)), adj_nb a b _⟩
  | u a b c => exact ⟨v a b, (mem_Phi _ _).2 (Or.inr (Or.inl ⟨a, b, rfl⟩)), adj_par' (u a b c) (by simp)⟩

theorem Phi_card (q : Fin 3 × (Fin 3 → Good)) : (Phi q).card = 97 := by
  classical
  have hle : (Phi q).card ≤ 97 := by
    unfold Phi
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_union_le (Finset.univ.image (fun p : Fin 3 × Fin 16 => v p.1 p.2))
      (Finset.univ.image (fun p : Fin 3 × Fin 16 => nb p.1 p.2 ((q.2 p.1).1 p.2)))
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3 × Fin 16)))
      (f := fun p : Fin 3 × Fin 16 => v p.1 p.2)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3 × Fin 16)))
      (f := fun p : Fin 3 × Fin 16 => nb p.1 p.2 ((q.2 p.1).1 p.2))
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1 h2
    omega
  exact le_antisymm hle (card_ge _ (Phi_tds q))

theorem Phi_inj : Function.Injective Phi := by
  rintro ⟨i, F⟩ ⟨i', F'⟩ h0
  have h := h0
  have hi : i = i' := by
    have hx : x i ∈ Phi (i', F') := h ▸ (mem_Phi _ _).2 (Or.inl rfl)
    rw [mem_Phi] at hx
    rcases hx with hx | ⟨a, b, hx⟩ | ⟨a, b, hx⟩
    · simpa using hx
    · cases hx
    · exact absurd hx.symm (nb_ne_x _ _ _ _)
  rw [hi] at h
  have hF : ∀ a b, (F a).1 b = (F' a).1 b := by
    intro a b
    have hm : nb a b ((F a).1 b) ∈ Phi (i', F') := h ▸ (mem_Phi _ _).2 (Or.inr (Or.inr ⟨a, b, rfl⟩))
    rw [mem_Phi] at hm
    rcases hm with hm | ⟨a', b', hm⟩ | ⟨a', b', hm⟩
    · exact absurd hm (nb_ne_x _ _ _ _)
    · exact absurd hm (nb_ne_v _ _ _ _ _)
    · obtain ⟨rfl, rfl⟩ := nb_row hm
      exact nb_inj a b hm
  have : F = F' := funext fun a => Subtype.ext (funext fun b => hF a b)
  rw [hi, this]

/-! ### The numbers -/

theorem gamma_eq : totalDominationNumber T = 97 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨Phi (0, fun _ => ⟨fun _ => 0, ⟨0, rfl⟩⟩), Phi_tds _, Phi_card _⟩
  · exact le_csInf ⟨97, Phi (0, fun _ => ⟨fun _ => 0, ⟨0, rfl⟩⟩), Phi_tds _, Phi_card _⟩
      (fun k ⟨D, hD, hk⟩ => hk ▸ card_ge D hD)

theorem num_ge : 3 * (4 ^ 16 - 3 ^ 16) ^ 3 ≤ numMinTotalDominating T := by
  classical
  have hcard : Nat.card (Fin 3 × (Fin 3 → Good)) = 3 * (4 ^ 16 - 3 ^ 16) ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, card_Good]; simp
  rw [← hcard, ← Set.ncard_univ]
  unfold numMinTotalDominating
  refine Set.ncard_le_ncard_of_injOn Phi ?_ (Phi_inj.injOn) (Set.toFinite _)
  intro q _
  exact ⟨Phi_tds q, by rw [Phi_card, gamma_eq]⟩

theorem bound_lt : ((((244 : ℕ) : ℝ) - ((97 : ℕ) : ℝ) / 2) / (((97 : ℕ) : ℝ) / 2)) ^
    (((97 : ℕ) : ℝ) / 2) < ((3 * (4 ^ 16 - 3 ^ 16) ^ 3 : ℕ) : ℝ) := by
  have hx : (((244 : ℕ) : ℝ) - ((97 : ℕ) : ℝ) / 2) / (((97 : ℕ) : ℝ) / 2) = 391 / 97 := by
    norm_num
  rw [hx, Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_natCast]
  have hs : 0 ≤ Real.sqrt (391 / 97) := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ ((3 * (4 ^ 16 - 3 ^ 16) ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← pow_lt_pow_iff_left₀ (pow_nonneg hs 97) hN (by norm_num : (2 : ℕ) ≠ 0)]
  have hsq : (Real.sqrt (391 / 97) ^ 97) ^ 2 = ((391 : ℝ) / 97) ^ 97 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [hsq]
  norm_num

end OMADisproofAux

open OMADisproofAux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_1804_10476.main) := by
  intro h
  have e := h Vx T T_isTree (by rw [card_Vx]; norm_num)
  rw [card_Vx, gamma_eq] at e
  have h1 : ((3 * (4 ^ 16 - 3 ^ 16) ^ 3 : ℕ) : ℝ) ≤ (numMinTotalDominating T : ℝ) :=
    Nat.cast_le.mpr num_ge
  have h2 := bound_lt
  push_cast at e h1 h2
  linarith
