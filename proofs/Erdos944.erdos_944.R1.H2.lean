import OMAReductions.R_Erdos944_erdos_944_R1
import Mathlib

/-!
Proof of the step `Erdos944.erdos_944.R1.H2`, the k = 5 case: for every r ≥ 2 a finite graph whose
vertex-deleted subgraphs are 4-colorable while deleting at most r edges never makes it 4-colorable.
The witness is the circulant G_{5,m,q} of Ema Skottova and Raphael Steiner, Critical edge sets in
vertex-critical graphs (arXiv:2508.08703), Theorem 4.1 with k = 5, m = 18 r + 3 and q = 24 r + 12.
Interface lemmas: V (Lemma 4.2), LINE (Lemma 4.3 on a window of integers), WRAP (Theorem 4.1).
Lean proof written November 27, 2026: V and WRAP by Claude Opus 5.5, LINE by Claude Fable 5.2,
skeleton and assembly by Claude Opus 5.5.
-/

namespace OMA.E944H2Proof

open Finset

/-- The distance set D of G_{5,m,q}: the odd numbers below 2m, and 2m, 2m + 1 shifted by
4 m j for j < q / 2. -/
def inD (m q d : ℕ) : Prop :=
  (d % 2 = 1 ∧ d < 2 * m) ∨
    ∃ j, j < q / 2 ∧ (d = 2 * m + 4 * m * j ∨ d = 2 * m + 1 + 4 * m * j)

/-- Cyclic distance on Fin N. -/
def cdist {N : ℕ} (x y : Fin N) : ℕ :=
  min ((y.val + N - x.val) % N) ((x.val + N - y.val) % N)

theorem cdist_comm {N : ℕ} (x y : Fin N) : cdist x y = cdist y x := by
  unfold cdist
  exact min_comm _ _

/-- The circulant graph G_{5,m,q} on N = 4 m q + 1 vertices. -/
def G (m q : ℕ) : SimpleGraph (Fin (4 * m * q + 1)) where
  Adj x y := x ≠ y ∧ inD m q (cdist x y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [cdist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The position (X - V - 1) mod (P + 1) of a vertex X ≠ V, without truncated subtraction. -/
theorem v_pos (P X V : ℕ) (hX : X < P + 1) (hV : V < P + 1) (hXV : X ≠ V) :
    (X < V ∧ (X + P - V) % (P + 1) + V = X + P) ∨
      (V < X ∧ (X + P - V) % (P + 1) + V + 1 = X) := by
  rcases Nat.lt_or_gt_of_ne hXV with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    refine ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The forward distance (Y - X) mod (P + 1) of two distinct vertices, without truncated
subtraction. -/
theorem v_dist (P X Y : ℕ) (hX : X < P + 1) (hY : Y < P + 1) (hXY : X ≠ Y) :
    (Y < X ∧ (Y + (P + 1) - X) % (P + 1) + X = Y + (P + 1)) ∨
      (X < Y ∧ (Y + (P + 1) - X) % (P + 1) + X = Y) := by
  rcases Nat.lt_or_gt_of_ne hXY with h | h
  · right
    refine ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · left
    refine ⟨h, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The quotient by 2 m of a number in the block [2 m k, 2 m k + 2 m). -/
theorem v_div (m s k : ℕ) (hm : 1 ≤ m) (h1 : 2 * m * k ≤ s) (h2 : s < 2 * m * k + 2 * m) :
    s / (2 * m) = k := by
  obtain ⟨e, rfl⟩ : ∃ e, s = e + 2 * m * k := ⟨s - 2 * m * k, by omega⟩
  rw [Nat.add_mul_div_left e k (by omega : 0 < 2 * m), Nat.div_eq_of_lt (by omega : e < 2 * m)]
  omega

/-- Shifting by multiples of 2 m shifts the quotient by 2 m accordingly. -/
theorem v_row (m s t k1 k2 : ℕ) (hm : 1 ≤ m) (h : t + 2 * m * k1 = s + 2 * m * k2) :
    t / (2 * m) + k1 = s / (2 * m) + k2 := by
  have h2m : 0 < 2 * m := by omega
  rw [← Nat.add_mul_div_left t k1 h2m, ← Nat.add_mul_div_left s k2 h2m, h]

/-- Jensen's coloring on positions 0, ..., 4 m q - 1: the color 2 * row + parity, with row the
parity of the block of length 2 m, differs at positions t = s + d or t = s + d - (4 m q + 1)
for every d in D. -/
theorem v_core (m q s t d : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) (hs : s < 4 * m * q)
    (hd : inD m q d) (hrel : t = s + d ∨ t + (4 * m * q + 1) = s + d) :
    2 * (s / (2 * m) % 2) + s % 2 ≠ 2 * (t / (2 * m) % 2) + t % 2 := by
  have e1 : 4 * m * q = 4 * (m * q) := by ring
  unfold inD at hd
  rcases hd with ⟨hodd, hlt⟩ | ⟨j, -, hj | hj⟩
  · rcases hrel with h | h
    · omega
    · obtain ⟨k, hk⟩ : ∃ k, 2 * q = k + 1 := ⟨2 * q - 1, by omega⟩
      have hk' : 2 * m * k + 2 * m = 4 * m * q := by
        have e3 : 4 * m * q = 2 * m * (2 * q) := by ring
        rw [e3, hk]
        ring
      rw [v_div m s k hm (by omega) (by omega), v_div m t 0 hm (by omega) (by omega)]
      omega
  · subst hj
    have e2 : 4 * m * j = 4 * (m * j) := by ring
    rcases hrel with h | h
    · have h' := v_row m s t 0 (1 + 2 * j) hm (by rw [h]; ring)
      omega
    · omega
  · subst hj
    have e2 : 4 * m * j = 4 * (m * j) := by ring
    rcases hrel with h | h
    · omega
    · have e3 : 2 * m * (2 * q) = 4 * m * q := by ring
      have e4 : 2 * m * (1 + 2 * j) = 2 * m + 4 * m * j := by ring
      have h' := v_row m s t (2 * q) (1 + 2 * j) hm (by omega)
      omega

/-- The coloring of `vertex_colorable` in coordinates: X, Y are the two ends of an edge and V is
the deleted vertex; the position of X is (X - V - 1) mod (4 m q + 1). -/
theorem v_key (m q X Y V : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) (hX : X < 4 * m * q + 1)
    (hY : Y < 4 * m * q + 1) (hV : V < 4 * m * q + 1) (hXV : X ≠ V) (hYV : Y ≠ V) (hXY : X ≠ Y)
    (hD : inD m q (min ((Y + (4 * m * q + 1) - X) % (4 * m * q + 1))
      ((X + (4 * m * q + 1) - Y) % (4 * m * q + 1)))) :
    2 * ((X + 4 * m * q - V) % (4 * m * q + 1) / (2 * m) % 2) +
        (X + 4 * m * q - V) % (4 * m * q + 1) % 2 ≠
      2 * ((Y + 4 * m * q - V) % (4 * m * q + 1) / (2 * m) % 2) +
        (Y + 4 * m * q - V) % (4 * m * q + 1) % 2 := by
  have cs := v_pos (4 * m * q) X V hX hV hXV
  generalize (X + 4 * m * q - V) % (4 * m * q + 1) = s at cs ⊢
  have hs : s < 4 * m * q := by omega
  have ct := v_pos (4 * m * q) Y V hY hV hYV
  generalize (Y + 4 * m * q - V) % (4 * m * q + 1) = t at ct ⊢
  have ht : t < 4 * m * q := by omega
  rcases min_choice ((Y + (4 * m * q + 1) - X) % (4 * m * q + 1))
      ((X + (4 * m * q + 1) - Y) % (4 * m * q + 1)) with h | h <;> rw [h] at hD <;> clear h
  · have c1 := v_dist (4 * m * q) X Y hX hY hXY
    generalize (Y + (4 * m * q + 1) - X) % (4 * m * q + 1) = d1 at c1 hD
    have hrel : t = s + d1 ∨ t + (4 * m * q + 1) = s + d1 := by omega
    exact v_core m q s t d1 hm hq hs hD hrel
  · have c2 := v_dist (4 * m * q) Y X hY hX (Ne.symm hXY)
    generalize (X + (4 * m * q + 1) - Y) % (4 * m * q + 1) = d2 at c2 hD
    have hrel : s = t + d2 ∨ s + (4 * m * q + 1) = t + d2 := by omega
    exact fun hc => v_core m q t s d2 hm hq ht hD hrel hc.symm

/-- V (Lemma 4.2 for k = 5): every vertex-deleted subgraph is 4-colorable. -/
theorem vertex_colorable (m q : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) (v : Fin (4 * m * q + 1)) :
    ∃ c : {x : Fin (4 * m * q + 1) // x ≠ v} → Fin 4,
      ∀ x y, (G m q).Adj x.val y.val → c x ≠ c y := by
  refine ⟨fun x => ⟨2 * ((x.val.val + 4 * m * q - v.val) % (4 * m * q + 1) / (2 * m) % 2) +
    (x.val.val + 4 * m * q - v.val) % (4 * m * q + 1) % 2, by omega⟩, ?_⟩
  intro x y hadj hc
  have hXY : x.val.val ≠ y.val.val := fun h => hadj.1 (Fin.ext h)
  have hXV : x.val.val ≠ v.val := fun h => x.property (Fin.ext h)
  have hYV : y.val.val ≠ v.val := fun h => y.property (Fin.ext h)
  exact v_key m q x.val.val y.val.val v.val hm hq x.val.isLt y.val.isLt v.isLt hXV hYV hXY
    hadj.2 (congrArg Fin.val hc)

/-
Helpers for `line_periodic` (prefix `ln_`), the k = 5 case of Lemma 4.3 of Skottova and Steiner,
with two shortcuts.
* Class structure, replacing the counting of Claim 4.4: walking along the cliques
  {y, y + 1, y + 2 m, y + 2 m + 1} inside the first 4 m positions shows that the positions of one
  parity carry two colors e1, e2 and those of the other parity carry the two other colors
  (`ln_base`). The expected color ψe is the 4m-periodic extension of ψ from the first 4 m
  positions; it changes under a shift by 2 m and differs on opposite parities (`ln_expected`).
* Claim 4.8 (`ln_two`): ψ y is ψe y or ψe (y - 1), because y has two neighbors among the first
  4 m positions, at distances 2 m + 4 m j and 2 m + 1 + 4 m j, of colors ψe (y - 2 m) and
  ψe (y - 2 m - 1).
* Final argument (`ln_final`), replacing Claim 4.9 and the counting of expected colors: let i + 1
  be the first position with ψ (i + 1) ≠ ψe (i + 1), and c = ψe i = ψ i = ψ (i + 1). Every k < m
  satisfies one of
    ψe (i + 2 k + 2 - 2 m) = c,   ψ (i + 2 k + 2) = c,   ψe (i + 2 k - 2 m) = c,
    ψ (i + 2 k + 1) = c,   ψ (i + 2 k + 1) = ψ (i + 2 k + 2),
  and each alternative yields a deleted pair (with partner i + 1, i + 1, i + 1, i, and the pair
  i + 2 k + 1, i + 2 k + 2 itself), injectively in k. Hence m ≤ 5 r, against 5 r < m.
Only the first 4 m positions need to be free of deleted pairs, and of the numerical hypotheses
only 5 r < m and 2 ≤ q are used.
-/

/-- Pigeonhole in Fin 4: a color different from two of four pairwise distinct colors is one of
the other two. -/
theorem ln_pigeon (a b c d t : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (hc : t ≠ c) (hd : t ≠ d) : t = a ∨ t = b := by
  rw [Ne, Fin.ext_iff] at hab hac had hbc hbd hcd hc hd
  rw [Fin.ext_iff, Fin.ext_iff]
  omega

/-- Induction in steps of 4 m on the integers above b. -/
theorem ln_ind (m : ℕ) (b : ℤ) (C : ℤ → Prop) (hm : 1 ≤ m)
    (h0 : ∀ y, b + 1 ≤ y → y ≤ b + 4 * m → C y)
    (h1 : ∀ y z, b + 1 ≤ y → z = y + 4 * m → C y → C z) : ∀ y, b + 1 ≤ y → C y := by
  have key : ∀ N : ℕ, ∀ y, b + 1 ≤ y → y ≤ b + N → C y := by
    intro N
    induction N with
    | zero => intro y h1 h2; omega
    | succ N ih =>
      intro y hy1 hy2
      by_cases h : y ≤ b + 4 * m
      · exact h0 y hy1 h
      · exact h1 (y - 4 * m) y (by omega) (by omega) (ih (y - 4 * m) (by omega) (by omega))
  intro y hy
  exact key (y - b).toNat y hy (by omega)

/-- Counting: an injective family of pairs inside T, indexed by the k < m with P k, has at most
card T members. -/
theorem ln_count (T : Finset (Sym2 ℤ)) (r : ℕ) (hTc : T.card ≤ r) (m : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (f g : ℕ → ℤ)
    (hmem : ∀ k, k < m → P k → s(f k, g k) ∈ T)
    (hinj : ∀ k k', k < m → k' < m → P k → P k' →
      (f k = f k' ∧ g k = g k') ∨ (f k = g k' ∧ g k = f k') → k = k') :
    ((Finset.range m).filter P).card ≤ r := by
  refine le_trans (Finset.card_le_card_of_injOn (fun k => s(f k, g k)) ?_ ?_) hTc
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    exact hmem k (Finset.mem_range.mp hk1) hk2
  · intro k hk k' hk' h
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1', hk2'⟩ := Finset.mem_filter.mp hk'
    exact hinj k k' (Finset.mem_range.mp hk1) (Finset.mem_range.mp hk1') hk2 hk2'
      (Sym2.eq_iff.mp h)

/-- Five sets of at most r indices cannot cover range m when 5 r < m. -/
theorem ln_five (m r : ℕ) (P1 P2 P3 P4 P5 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2]
    [DecidablePred P3] [DecidablePred P4] [DecidablePred P5]
    (h1 : ((Finset.range m).filter P1).card ≤ r) (h2 : ((Finset.range m).filter P2).card ≤ r)
    (h3 : ((Finset.range m).filter P3).card ≤ r) (h4 : ((Finset.range m).filter P4).card ≤ r)
    (h5 : ((Finset.range m).filter P5).card ≤ r)
    (hcover : ∀ k, k < m → P1 k ∨ P2 k ∨ P3 k ∨ P4 k ∨ P5 k) : m ≤ 5 * r := by
  have hsub : Finset.range m ⊆ (Finset.range m).filter P1 ∪ ((Finset.range m).filter P2 ∪
      ((Finset.range m).filter P3 ∪ ((Finset.range m).filter P4 ∪
        (Finset.range m).filter P5))) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hcover k hk' with h | h | h | h | h
    · exact Or.inl ⟨hk, h⟩
    · exact Or.inr (Or.inl ⟨hk, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hk, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, h⟩)))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  have u1 := Finset.card_union_le ((Finset.range m).filter P1) ((Finset.range m).filter P2 ∪
      ((Finset.range m).filter P3 ∪ ((Finset.range m).filter P4 ∪ (Finset.range m).filter P5)))
  have u2 := Finset.card_union_le ((Finset.range m).filter P2)
      ((Finset.range m).filter P3 ∪ ((Finset.range m).filter P4 ∪ (Finset.range m).filter P5))
  have u3 := Finset.card_union_le ((Finset.range m).filter P3)
      ((Finset.range m).filter P4 ∪ (Finset.range m).filter P5)
  have u4 := Finset.card_union_le ((Finset.range m).filter P4) ((Finset.range m).filter P5)
  omega

/-- The edges with an endpoint among the first 4 m positions, in a form suited to omega. -/
theorem ln_edges (m q : ℕ) (ψ : ℤ → Fin 4) (b U : ℤ)
    (hA : ∀ x y, b + 1 ≤ x → x ≤ b + 4 * m → b + 1 ≤ y → y ≤ U → inD m q (x - y).natAbs →
      ψ x ≠ ψ y) :
    (∀ x y, b + 1 ≤ x → x ≤ b + 4 * m → b + 1 ≤ y → y ≤ U → (x - y) % 2 = 1 → x - y < 2 * m →
      y - x < 2 * m → ψ x ≠ ψ y) ∧
    (∀ x y (j : ℕ), b + 1 ≤ x → x ≤ b + 4 * m → y ≤ U → j < q / 2 →
      (y = x + 2 * m + ((4 * m * j : ℕ) : ℤ) ∨ y = x + 2 * m + 1 + ((4 * m * j : ℕ) : ℤ)) →
      ψ x ≠ ψ y) := by
  constructor
  · intro x y h1 h2 h3 h4 h5 h6 h7
    exact hA x y h1 h2 h3 h4 (Or.inl ⟨by omega, by omega⟩)
  · intro x y j h1 h2 h3 hj h
    refine hA x y h1 h2 (by omega) h3 (Or.inr ⟨j, hj, ?_⟩)
    omega

/-- Class structure on the first 4 m positions: the positions y and y + 2 m carry the two colors
e1, e2 when y - b - 1 is even, and the two other colors when it is odd. -/
theorem ln_base (m q : ℕ) (hm : 1 ≤ m) (hq : 0 < q / 2) (ψ : ℤ → Fin 4) (b U : ℤ)
    (hU4 : b + 4 * m ≤ U) (e1 e2 : Fin 4)
    (he1 : ψ (b + 1) = e1) (he2 : ψ (b + 1 + 2 * m) = e2)
    (H1 : ∀ x y, b + 1 ≤ x → x ≤ b + 4 * m → b + 1 ≤ y → y ≤ U → (x - y) % 2 = 1 →
      x - y < 2 * m → y - x < 2 * m → ψ x ≠ ψ y)
    (H2 : ∀ x y (j : ℕ), b + 1 ≤ x → x ≤ b + 4 * m → y ≤ U → j < q / 2 →
      (y = x + 2 * m + ((4 * m * j : ℕ) : ℤ) ∨ y = x + 2 * m + 1 + ((4 * m * j : ℕ) : ℤ)) →
      ψ x ≠ ψ y) :
    ∀ y, b + 1 ≤ y → y ≤ b + 2 * m → ∀ z, z = y + 2 * m →
      ((y - b - 1) % 2 = 0 → (ψ y = e1 ∧ ψ z = e2) ∨ (ψ y = e2 ∧ ψ z = e1)) ∧
      ((y - b - 1) % 2 = 1 → ψ y ≠ e1 ∧ ψ y ≠ e2 ∧ ψ z ≠ e1 ∧ ψ z ≠ e2) := by
  have he : e1 ≠ e2 := by
    rw [← he1, ← he2]
    exact H2 (b + 1) (b + 1 + 2 * m) 0 (by omega) (by omega) (by omega) hq (Or.inl (by omega))
  intro y hy
  induction y, hy using Int.leInduction with
  | base =>
    intro _ z hz
    subst hz
    exact ⟨fun _ => Or.inl ⟨he1, he2⟩, fun h => by omega⟩
  | succ y hy ih =>
    intro hy2 z hz
    obtain ⟨ih0, ih1⟩ := ih (by omega) (y + 2 * m) rfl
    have k1 : ψ y ≠ ψ (y + 1) :=
      H1 y (y + 1) hy (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have k2 : ψ y ≠ ψ (y + 2 * m) :=
      H2 y (y + 2 * m) 0 hy (by omega) (by omega) hq (Or.inl (by omega))
    have k3 : ψ y ≠ ψ z :=
      H2 y z 0 hy (by omega) (by omega) hq (Or.inr (by omega))
    have k4 : ψ (y + 1) ≠ ψ (y + 2 * m) :=
      H1 (y + 1) (y + 2 * m) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    have k5 : ψ (y + 1) ≠ ψ z :=
      H2 (y + 1) z 0 (by omega) (by omega) (by omega) hq (Or.inl (by omega))
    have k6 : ψ (y + 2 * m) ≠ ψ z :=
      H1 (y + 2 * m) z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    constructor
    · intro hpar
      obtain ⟨a1, a2, a3, a4⟩ := ih1 (by omega)
      have p1 := ln_pigeon e1 e2 (ψ y) (ψ (y + 2 * m)) (ψ (y + 1)) he (Ne.symm a1) (Ne.symm a3)
        (Ne.symm a2) (Ne.symm a4) k2 (Ne.symm k1) k4
      have p2 := ln_pigeon e1 e2 (ψ y) (ψ (y + 2 * m)) (ψ z) he (Ne.symm a1) (Ne.symm a3)
        (Ne.symm a2) (Ne.symm a4) k2 (Ne.symm k3) (Ne.symm k6)
      rcases p1 with p1 | p1 <;> rcases p2 with p2 | p2
      · exact absurd (p1.trans p2.symm) k5
      · exact Or.inl ⟨p1, p2⟩
      · exact Or.inr ⟨p1, p2⟩
      · exact absurd (p1.trans p2.symm) k5
    · intro hpar
      rcases ih0 (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [a1] at k1 k3
        rw [a2] at k4 k6
        exact ⟨Ne.symm k1, k4, Ne.symm k3, Ne.symm k6⟩
      · rw [a1] at k1 k3
        rw [a2] at k4 k6
        exact ⟨k4, Ne.symm k1, Ne.symm k6, Ne.symm k3⟩

/-- The expected colors: a 4m-periodic ψe agreeing with ψ on the first 4 m positions changes
under a shift by 2 m, differs on positions of opposite parity, and is read off the first 4 m
positions. -/
theorem ln_expected (m q : ℕ) (hm : 1 ≤ m) (hq : 0 < q / 2) (ψ ψe : ℤ → Fin 4) (b U : ℤ)
    (hU4 : b + 4 * m ≤ U)
    (hE1 : ∀ y, ψe (y + 4 * m) = ψe y)
    (hE2 : ∀ y, b + 1 ≤ y → y ≤ b + 4 * m → ψe y = ψ y)
    (H1 : ∀ x y, b + 1 ≤ x → x ≤ b + 4 * m → b + 1 ≤ y → y ≤ U → (x - y) % 2 = 1 →
      x - y < 2 * m → y - x < 2 * m → ψ x ≠ ψ y)
    (H2 : ∀ x y (j : ℕ), b + 1 ≤ x → x ≤ b + 4 * m → y ≤ U → j < q / 2 →
      (y = x + 2 * m + ((4 * m * j : ℕ) : ℤ) ∨ y = x + 2 * m + 1 + ((4 * m * j : ℕ) : ℤ)) →
      ψ x ≠ ψ y) :
    (∀ y z, b + 1 ≤ y → z = y + 2 * m → ψe z ≠ ψe y) ∧
    (∀ y y', b + 1 ≤ y → b + 1 ≤ y' → (y - y') % 2 = 1 → ψe y ≠ ψe y') ∧
    (∀ y, b + 1 ≤ y → ∃ n, ∃ j : ℕ, b + 1 ≤ n ∧ n ≤ b + 4 * m ∧
      y = n + ((4 * m * j : ℕ) : ℤ) ∧ ψe y = ψ n) := by
  have hB := ln_base m q hm hq ψ b U hU4 (ψ (b + 1)) (ψ (b + 1 + 2 * m)) rfl rfl H1 H2
  have hP : ∀ y, b + 1 ≤ y →
      ((ψe y = ψ (b + 1) ∨ ψe y = ψ (b + 1 + 2 * m)) ↔ (y - b - 1) % 2 = 0) := by
    refine ln_ind m b _ hm ?_ ?_
    · intro y hy1 hy2
      rw [hE2 y hy1 hy2]
      by_cases h : y ≤ b + 2 * m
      · obtain ⟨c0, c1⟩ := hB y hy1 h (y + 2 * m) rfl
        constructor
        · intro hc
          by_contra hne
          obtain ⟨d1, d2, -, -⟩ := c1 (by omega)
          rcases hc with hc | hc
          · exact d1 hc
          · exact d2 hc
        · intro hpar
          rcases c0 hpar with ⟨d1, -⟩ | ⟨d1, -⟩
          · exact Or.inl d1
          · exact Or.inr d1
      · obtain ⟨c0, c1⟩ := hB (y - 2 * m) (by omega) (by omega) y (by omega)
        constructor
        · intro hc
          by_contra hne
          obtain ⟨-, -, d1, d2⟩ := c1 (by omega)
          rcases hc with hc | hc
          · exact d1 hc
          · exact d2 hc
        · intro hpar
          rcases c0 (by omega) with ⟨-, d1⟩ | ⟨-, d1⟩
          · exact Or.inr d1
          · exact Or.inl d1
    · intro y z hy hz ih
      rw [hz, hE1 y]
      constructor
      · intro hc
        have := ih.mp hc
        omega
      · intro hpar
        exact ih.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have hG : ∀ y, b + 1 ≤ y → ψe (y + 2 * m) ≠ ψe y := by
      refine ln_ind m b _ hm ?_ ?_
      · intro y hy1 hy2
        by_cases h : y ≤ b + 2 * m
        · rw [hE2 y hy1 hy2, hE2 (y + 2 * m) (by omega) (by omega)]
          exact Ne.symm (H2 y (y + 2 * m) 0 hy1 hy2 (by omega) hq (Or.inl (by omega)))
        · have e : ψe (y + 2 * m) = ψe (y - 2 * m) := by
            have := hE1 (y - 2 * m)
            rw [show y - 2 * (m : ℤ) + 4 * m = y + 2 * m by ring] at this
            exact this
          rw [e, hE2 y hy1 hy2, hE2 (y - 2 * m) (by omega) (by omega)]
          exact H2 (y - 2 * m) y 0 (by omega) (by omega) (by omega) hq (Or.inl (by omega))
      · intro y z hy hz ih
        have e : ψe (z + 2 * m) = ψe (y + 2 * m) := by
          have := hE1 (y + 2 * m)
          rw [show y + 2 * (m : ℤ) + 4 * m = z + 2 * m by rw [hz]; ring] at this
          exact this
        rw [e, hz, hE1 y]
        exact ih
    intro y z hy hz
    rw [hz]
    exact hG y hy
  · intro y y' hy hy' hpar h
    have h1 := hP y hy
    have h2 := hP y' hy'
    rw [h] at h1
    have h3 := h1.symm.trans h2
    omega
  · refine ln_ind m b _ hm ?_ ?_
    · intro y hy1 hy2
      exact ⟨y, 0, hy1, hy2, by simp, hE2 y hy1 hy2⟩
    · intro y z hy hz ih
      obtain ⟨n, j, hn1, hn2, hyn, he⟩ := ih
      refine ⟨n, j + 1, hn1, hn2, ?_, ?_⟩
      · rw [hz, hyn]
        push_cast
        ring
      · rw [hz, hE1 y]
        exact he

/-- Claim 4.8 for k = 5: every position of the window has its expected color or the expected
color of its predecessor. -/
theorem ln_two (m q : ℕ) (hm : 1 ≤ m) (ψ ψe : ℤ → Fin 4) (b U : ℤ)
    (hUq : ∀ j : ℕ, b + 2 * m + ((4 * m * j : ℕ) : ℤ) < U → j < q / 2)
    (hE2 : ∀ y, b + 1 ≤ y → y ≤ b + 4 * m → ψe y = ψ y)
    (H2 : ∀ x y (j : ℕ), b + 1 ≤ x → x ≤ b + 4 * m → y ≤ U → j < q / 2 →
      (y = x + 2 * m + ((4 * m * j : ℕ) : ℤ) ∨ y = x + 2 * m + 1 + ((4 * m * j : ℕ) : ℤ)) →
      ψ x ≠ ψ y)
    (G1 : ∀ y z, b + 1 ≤ y → z = y + 2 * m → ψe z ≠ ψe y)
    (Go : ∀ y y', b + 1 ≤ y → b + 1 ≤ y' → (y - y') % 2 = 1 → ψe y ≠ ψe y')
    (GR : ∀ y, b + 1 ≤ y → ∃ n, ∃ j : ℕ, b + 1 ≤ n ∧ n ≤ b + 4 * m ∧
      y = n + ((4 * m * j : ℕ) : ℤ) ∧ ψe y = ψ n) :
    ∀ y z, b + 1 ≤ y → y ≤ U → z = y - 1 → ψ y = ψe y ∨ ψ y = ψe z := by
  intro y z hy1 hy2 hz
  by_cases h : y ≤ b + 4 * m
  · exact Or.inl (hE2 y hy1 h).symm
  · obtain ⟨n1, j1, hn1a, hn1b, hyn1, he1⟩ := GR (y - 2 * m) (by omega)
    obtain ⟨n2, j2, hn2a, hn2b, hyn2, he2⟩ := GR (y - 2 * m - 1) (by omega)
    have c1 : ψ y ≠ ψe (y - 2 * m) := by
      rw [he1]
      exact Ne.symm (H2 n1 y j1 hn1a hn1b hy2 (hUq j1 (by omega)) (Or.inl (by omega)))
    have c2 : ψ y ≠ ψe (y - 2 * m - 1) := by
      rw [he2]
      exact Ne.symm (H2 n2 y j2 hn2a hn2b hy2 (hUq j2 (by omega)) (Or.inr (by omega)))
    exact ln_pigeon (ψe y) (ψe z) (ψe (y - 2 * m)) (ψe (y - 2 * m - 1)) (ψ y)
      (Go y z hy1 (by omega) (by omega))
      (G1 (y - 2 * m) y (by omega) (by omega))
      (Go y (y - 2 * m - 1) hy1 (by omega) (by omega))
      (Go z (y - 2 * m) (by omega) (by omega) (by omega))
      (G1 (y - 2 * m - 1) z (by omega) (by omega))
      (Go (y - 2 * m) (y - 2 * m - 1) (by omega) (by omega) (by omega))
      c1 c2

/-- The final argument: a first position whose color is not the expected one cannot exist.
With c the expected color of i, each k < m lies in one of five sets of at most r indices. -/
theorem ln_final (r m : ℕ) (hm : 5 * r < m) (ψ ψe : ℤ → Fin 4) (b U : ℤ)
    (T : Finset (Sym2 ℤ)) (hTc : T.card ≤ r)
    (hT : ∀ x y, b + 1 ≤ x → x ≤ U → b + 1 ≤ y → y ≤ U → (x - y) % 2 = 1 → x - y < 2 * m →
      y - x < 2 * m → ψ x = ψ y → s(x, y) ∈ T)
    (h2 : ∀ y z, b + 1 ≤ y → y ≤ U → z = y - 1 → ψ y = ψe y ∨ ψ y = ψe z)
    (G1 : ∀ y z, b + 1 ≤ y → z = y + 2 * m → ψe z ≠ ψe y)
    (Gs : ∀ y y' z, b + 1 ≤ y → b + 1 ≤ y' → (y - y') % 2 = 0 → z = y' + 2 * m →
      ψe y = ψe y' ∨ ψe y = ψe z)
    (i : ℤ) (hi1 : b + 4 * m ≤ i) (hi2 : i + 2 * m ≤ U)
    (hmin : ∀ y, b + 1 ≤ y → y ≤ i → ψ y = ψe y) (hbad : ψ (i + 1) ≠ ψe (i + 1)) : False := by
  have hc1 : ψ i = ψe i := hmin i (by omega) le_rfl
  have hc2 : ψ (i + 1) = ψe i := by
    rcases h2 (i + 1) i (by omega) (by omega) (by omega) with h | h
    · exact absurd h hbad
    · exact h
  have hflip : ∀ y z, b + 1 ≤ z → y = z + 2 * m → (i - z) % 2 = 0 →
      (ψe y = ψe i ↔ ψe z ≠ ψe i) := by
    intro y z hz hy hpar
    have h1 := G1 z y hz hy
    have h3 := Gs i z y (by omega) hz hpar hy
    constructor
    · intro h h'
      exact h1 (h.trans h'.symm)
    · intro h
      rcases h3 with h3 | h3
      · exact absurd h3.symm h
      · exact h3.symm
  have hne : ∀ z, z = i - 2 * m → ψe z ≠ ψe i := by
    intro z hz h
    exact G1 z i (by omega) (by omega) h.symm
  have hK1 := ln_count T r hTc m (fun k : ℕ => ψe (i + 2 * (k : ℤ) + 2 - 2 * m) = ψe i)
    (fun _ => i + 1) (fun k => i + 2 * (k : ℤ) + 2 - 2 * m)
    (by
      intro k hk hP
      refine hT (i + 1) (i + 2 * (k : ℤ) + 2 - 2 * m) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) ?_
      rw [hc2, hmin (i + 2 * (k : ℤ) + 2 - 2 * m) (by omega) (by omega)]
      exact hP.symm)
    (by
      intro k k' hk hk' hP hP' h
      omega)
  have hK2 := ln_count T r hTc m (fun k : ℕ => ψ (i + 2 * (k : ℤ) + 2) = ψe i)
    (fun _ => i + 1) (fun k => i + 2 * (k : ℤ) + 2)
    (by
      intro k hk hP
      refine hT (i + 1) (i + 2 * (k : ℤ) + 2) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) ?_
      rw [hc2]
      exact hP.symm)
    (by
      intro k k' hk hk' hP hP' h
      omega)
  have hK3 := ln_count T r hTc m (fun k : ℕ => ψe (i + 2 * (k : ℤ) - 2 * m) = ψe i)
    (fun _ => i + 1) (fun k => i + 2 * (k : ℤ) - 2 * m)
    (by
      intro k hk hP
      have hk0 : k ≠ 0 := by
        intro h0
        exact hne (i + 2 * (k : ℤ) - 2 * m) (by omega) hP
      refine hT (i + 1) (i + 2 * (k : ℤ) - 2 * m) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) ?_
      rw [hc2, hmin (i + 2 * (k : ℤ) - 2 * m) (by omega) (by omega)]
      exact hP.symm)
    (by
      intro k k' hk hk' hP hP' h
      omega)
  have hK4 := ln_count T r hTc m (fun k : ℕ => ψ (i + 2 * (k : ℤ) + 1) = ψe i)
    (fun _ => i) (fun k => i + 2 * (k : ℤ) + 1)
    (by
      intro k hk hP
      refine hT i (i + 2 * (k : ℤ) + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) ?_
      rw [hc1]
      exact hP.symm)
    (by
      intro k k' hk hk' hP hP' h
      omega)
  have hK5 := ln_count T r hTc m
    (fun k : ℕ => ψ (i + 2 * (k : ℤ) + 1) = ψ (i + 2 * (k : ℤ) + 2))
    (fun k => i + 2 * (k : ℤ) + 1) (fun k => i + 2 * (k : ℤ) + 2)
    (by
      intro k hk hP
      exact hT (i + 2 * (k : ℤ) + 1) (i + 2 * (k : ℤ) + 2) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hP)
    (by
      intro k k' hk hk' hP hP' h
      omega)
  have hcover : ∀ k : ℕ, k < m →
      ψe (i + 2 * (k : ℤ) + 2 - 2 * m) = ψe i ∨ ψ (i + 2 * (k : ℤ) + 2) = ψe i ∨
      ψe (i + 2 * (k : ℤ) - 2 * m) = ψe i ∨ ψ (i + 2 * (k : ℤ) + 1) = ψe i ∨
      ψ (i + 2 * (k : ℤ) + 1) = ψ (i + 2 * (k : ℤ) + 2) := by
    intro k hk
    by_contra hnot
    simp only [not_or] at hnot
    obtain ⟨n1, n2, n3, n4, n5⟩ := hnot
    have ey : ψe (i + 2 * (k : ℤ) + 2) = ψe i :=
      (hflip (i + 2 * k + 2) (i + 2 * k + 2 - 2 * m) (by omega) (by omega) (by omega)).mpr n1
    have ew : ψe (i + 2 * (k : ℤ)) = ψe i :=
      (hflip (i + 2 * k) (i + 2 * k - 2 * m) (by omega) (by omega) (by omega)).mpr n3
    have ay : ψ (i + 2 * (k : ℤ) + 2) = ψe (i + 2 * k + 1) := by
      rcases h2 (i + 2 * k + 2) (i + 2 * k + 1) (by omega) (by omega) (by omega) with h | h
      · exact absurd (h.trans ey) n2
      · exact h
    have ax : ψ (i + 2 * (k : ℤ) + 1) = ψe (i + 2 * k + 1) := by
      rcases h2 (i + 2 * k + 1) (i + 2 * k) (by omega) (by omega) (by omega) with h | h
      · exact h
      · exact absurd (h.trans ew) n4
    exact n5 (ax.trans ay.symm)
  have h5 := ln_five m r _ _ _ _ _ hK1 hK2 hK3 hK4 hK5 hcover
  omega

/-- Lemma 4.3 on an abstract window from b + 1 to U: every position up to U - 2 m + 1 has its
expected color. -/
theorem ln_core (r m q : ℕ) (hm : 5 * r < m) (hq : 0 < q / 2) (ψ ψe : ℤ → Fin 4) (b U : ℤ)
    (hU4 : b + 4 * m ≤ U)
    (hUq : ∀ j : ℕ, b + 2 * m + ((4 * m * j : ℕ) : ℤ) < U → j < q / 2)
    (T : Finset (Sym2 ℤ)) (hTc : T.card ≤ r)
    (hA : ∀ x y, b + 1 ≤ x → x ≤ b + 4 * m → b + 1 ≤ y → y ≤ U → inD m q (x - y).natAbs →
      ψ x ≠ ψ y)
    (hT : ∀ x y, b + 1 ≤ x → x ≤ U → b + 1 ≤ y → y ≤ U → inD m q (x - y).natAbs → ψ x = ψ y →
      s(x, y) ∈ T)
    (hE1 : ∀ y, ψe (y + 4 * m) = ψe y)
    (hE2 : ∀ y, b + 1 ≤ y → y ≤ b + 4 * m → ψe y = ψ y) :
    ∀ y, b + 1 ≤ y → y + 2 * m ≤ U + 1 → ψ y = ψe y := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨H1, H2⟩ := ln_edges m q ψ b U hA
  obtain ⟨G1, Go, GR⟩ := ln_expected m q hm1 hq ψ ψe b U hU4 hE1 hE2 H1 H2
  have h2 := ln_two m q hm1 ψ ψe b U hUq hE2 H2 G1 Go GR
  have Gs : ∀ y y' z, b + 1 ≤ y → b + 1 ≤ y' → (y - y') % 2 = 0 → z = y' + 2 * m →
      ψe y = ψe y' ∨ ψe y = ψe z := by
    intro y y' z hy hy' hpar hz
    exact ln_pigeon (ψe y') (ψe z) (ψe (y' + 1)) (ψe (y' + 1 + 2 * m)) (ψe y)
      (Ne.symm (G1 y' z hy' hz))
      (Go y' (y' + 1) hy' (by omega) (by omega))
      (Go y' (y' + 1 + 2 * m) hy' (by omega) (by omega))
      (Go z (y' + 1) (by omega) (by omega) (by omega))
      (Go z (y' + 1 + 2 * m) (by omega) (by omega) (by omega))
      (Ne.symm (G1 (y' + 1) (y' + 1 + 2 * m) (by omega) rfl))
      (Go y (y' + 1) hy (by omega) (by omega))
      (Go y (y' + 1 + 2 * m) hy (by omega) (by omega))
  have hT' : ∀ x y, b + 1 ≤ x → x ≤ U → b + 1 ≤ y → y ≤ U → (x - y) % 2 = 1 → x - y < 2 * m →
      y - x < 2 * m → ψ x = ψ y → s(x, y) ∈ T := by
    intro x y h1 h2 h3 h4 h5 h6 h7 h8
    exact hT x y h1 h2 h3 h4 (Or.inl ⟨by omega, by omega⟩) h8
  have key : ∀ N : ℕ, ∀ y, b + 1 ≤ y → y ≤ b + N → y + 2 * m ≤ U + 1 → ψ y = ψe y := by
    intro N
    induction N with
    | zero => intro y h1 h2; omega
    | succ N ih =>
      intro y hy1 hy2 hy3
      by_cases h : y ≤ b + 4 * m
      · exact (hE2 y hy1 h).symm
      · by_contra hbad
        refine ln_final r m hm ψ ψe b U T hTc hT' h2 G1 Gs (y - 1) (by omega) (by omega) ?_ ?_
        · intro y' h1 h2
          exact ih y' h1 (by omega) (by omega)
        · rw [sub_add_cancel]
          exact hbad
  intro y hy1 hy2
  exact key (y - b).toNat y hy1 (by omega) hy2

/-- LINE (Lemma 4.3 for k = 5, on a window of integers): a coloring that is proper on all pairs
of the window at a distance in D, except the deleted pairs (at most r of them), and whose first
12 m positions meet no deleted pair, is 4m-periodic on the first m q positions. -/
theorem line_periodic (r m q : ℕ) (hm : 18 * r + 2 < m) (hq : 24 * r + 12 ≤ q) (h4 : 4 ∣ q)
    (ψ : ℤ → Fin 4) (del : ℤ → ℤ → Prop) (b : ℤ)
    (hsymm : ∀ i j, del i j → del j i)
    (hT : ∃ T : Finset (Sym2 ℤ), T.card ≤ r ∧ ∀ i j, b + 1 ≤ i → i ≤ b + 2 * m * q →
      b + 1 ≤ j → j ≤ b + 2 * m * q → del i j → s(i, j) ∈ T)
    (hprop : ∀ i j, b + 1 ≤ i → i ≤ b + 2 * m * q → b + 1 ≤ j → j ≤ b + 2 * m * q →
      inD m q (i - j).natAbs → ¬ del i j → ψ i ≠ ψ j)
    (hS : ∀ i j, del i j → ¬ (b + 1 ≤ i ∧ i ≤ b + 12 * m)) :
    ∀ i, b + 1 ≤ i → i + 4 * m ≤ b + m * q → ψ (i + 4 * m) = ψ i := by
  -- hsymm is not needed: every deleted pair is tested with its endpoint in S first.
  have _ := hsymm
  obtain ⟨T, hTc, hT⟩ := hT
  have hmq : (2 : ℤ) * m ≤ m * q := by
    have h : m * 2 ≤ m * q := Nat.mul_le_mul_left m (by omega)
    have h' : ((m * 2 : ℕ) : ℤ) ≤ ((m * q : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hL : (2 : ℤ) * m * q = 2 * (m * q) := by ring
  have hE1 : ∀ y : ℤ, ψ (b + 1 + (y + 4 * m - b - 1) % (4 * m)) =
      ψ (b + 1 + (y - b - 1) % (4 * m)) := by
    intro y
    rw [show y + 4 * (m : ℤ) - b - 1 = (y - b - 1) + 4 * m by ring, Int.add_emod_right]
  have key := ln_core r m q (by omega) (by omega) ψ (fun y => ψ (b + 1 + (y - b - 1) % (4 * m))) b
    (b + 2 * m * q) (by omega)
    (by
      intro j hj
      by_contra hc
      have h : m * q ≤ m * (2 * j + 1) := Nat.mul_le_mul_left m (by omega)
      have h' : ((m * q : ℕ) : ℤ) ≤ ((m * (2 * j + 1) : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at h' hj
      linarith)
    T hTc
    (by
      intro x y h1 h2 h3 h4 hD
      exact hprop x y h1 (by omega) h3 h4 hD (fun hd => hS x y hd ⟨h1, by omega⟩))
    (by
      intro x y h1 h2 h3 h4 hD he
      by_contra hn
      exact hprop x y h1 h2 h3 h4 hD (fun hd => hn (hT x y h1 h2 h3 h4 hd)) he)
    hE1
    (by
      intro y h1 h2
      show ψ (b + 1 + (y - b - 1) % (4 * m)) = ψ y
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      congr 1
      ring)
  intro i hi1 hi2
  have a1 := key (i + 4 * m) (by omega) (by omega)
  have a2 := key i hi1 (by omega)
  rw [a1, a2]
  exact hE1 i

/-- Reduction of an integer modulo n + 1. -/
def w_red (n : ℕ) (i : ℤ) : Fin (n + 1) :=
  ⟨(i % ((n : ℤ) + 1)).toNat, by
    have h1 : 0 ≤ i % ((n : ℤ) + 1) := Int.emod_nonneg _ (by omega)
    have h2 : i % ((n : ℤ) + 1) < (n : ℤ) + 1 := Int.emod_lt_of_pos _ (by omega)
    omega⟩

/-- As an integer, `w_red n i` is `i % (n + 1)`. -/
theorem w_red_val (n : ℕ) (i : ℤ) : ((w_red n i).val : ℤ) = i % ((n : ℤ) + 1) := by
  have h1 : 0 ≤ i % ((n : ℤ) + 1) := Int.emod_nonneg _ (by omega)
  show (((i % ((n : ℤ) + 1)).toNat : ℕ) : ℤ) = _
  exact Int.toNat_of_nonneg h1

/-- Shifting by n + 1 does not change the reduction. -/
theorem w_red_add (n : ℕ) (i : ℤ) : w_red n (i + ((n : ℤ) + 1)) = w_red n i := by
  apply Fin.ext
  have h1 := w_red_val n (i + ((n : ℤ) + 1))
  have h2 := w_red_val n i
  have h3 : (i + ((n : ℤ) + 1)) % ((n : ℤ) + 1) = i % ((n : ℤ) + 1) := by
    have : i + ((n : ℤ) + 1) = i + ((n : ℤ) + 1) * 1 := by ring
    rw [this, Int.add_mul_emod_self_left]
  omega

/-- Two integers less than n + 1 apart with the same reduction are equal. -/
theorem w_red_inj (n : ℕ) (x y : ℤ) (h1 : x - y < (n : ℤ) + 1) (h2 : y - x < (n : ℤ) + 1)
    (h : w_red n x = w_red n y) : x = y := by
  have hx := w_red_val n x
  have hy := w_red_val n y
  have hv : x % ((n : ℤ) + 1) = y % ((n : ℤ) + 1) := by rw [← hx, ← hy, h]
  have ex := Int.mul_ediv_add_emod x ((n : ℤ) + 1)
  have ey := Int.mul_ediv_add_emod y ((n : ℤ) + 1)
  have hk : x - y = ((n : ℤ) + 1) * (x / ((n : ℤ) + 1) - y / ((n : ℤ) + 1)) := by
    linear_combination ey - ex + hv
  have hn : (0 : ℤ) ≤ n := by positivity
  rcases lt_trichotomy (x / ((n : ℤ) + 1) - y / ((n : ℤ) + 1)) 0 with hk' | hk' | hk'
  · have : x / ((n : ℤ) + 1) - y / ((n : ℤ) + 1) ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℤ) ≤ (n : ℤ) + 1)
    linarith
  · rw [hk', mul_zero] at hk
    linarith
  · have : 1 ≤ x / ((n : ℤ) + 1) - y / ((n : ℤ) + 1) := by omega
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℤ) ≤ (n : ℤ) + 1)
    linarith

/-- For x ≤ y less than half the cycle apart, the cyclic distance of the reductions is y - x. -/
theorem w_cdist_red_le (n : ℕ) (x y : ℤ) (h0 : 0 ≤ y - x) (h1 : 2 * (y - x) < (n : ℤ) + 1) :
    cdist (w_red n x) (w_red n y) = (y - x).toNat := by
  have hx := w_red_val n x
  have hy := w_red_val n y
  have hxl := (w_red n x).isLt
  have hyl := (w_red n y).isLt
  have ex := Int.mul_ediv_add_emod x ((n : ℤ) + 1)
  have ey := Int.mul_ediv_add_emod y ((n : ℤ) + 1)
  have hd : y - x < (n : ℤ) + 1 := by linarith
  unfold cdist
  generalize (w_red n x).val = A at hx hxl
  generalize (w_red n y).val = B at hy hyl
  have sB : ((B + (n + 1) - A : ℕ) : ℤ) = (B : ℤ) + ((n : ℤ) + 1) - (A : ℤ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have sA : ((A + (n + 1) - B : ℕ) : ℤ) = (A : ℤ) + ((n : ℤ) + 1) - (B : ℤ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have e1 : (((B + (n + 1) - A) % (n + 1) : ℕ) : ℤ) = y - x := by
    have hc : ((B + (n + 1) - A : ℕ) : ℤ) =
        (y - x) + ((n : ℤ) + 1) * (1 + x / ((n : ℤ) + 1) - y / ((n : ℤ) + 1)) := by
      rw [sB, hx, hy]
      linear_combination ey - ex
    rw [Int.natCast_emod, hc]
    push_cast
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 hd]
  have e2 : (((A + (n + 1) - B) % (n + 1) : ℕ) : ℤ) =
      (((n : ℤ) + 1) - (y - x)) % ((n : ℤ) + 1) := by
    have hc : ((A + (n + 1) - B : ℕ) : ℤ) =
        (((n : ℤ) + 1) - (y - x)) + ((n : ℤ) + 1) * (y / ((n : ℤ) + 1) - x / ((n : ℤ) + 1)) := by
      rw [sA, hx, hy]
      linear_combination ex - ey
    rw [Int.natCast_emod, hc]
    push_cast
    rw [Int.add_mul_emod_self_left]
  clear hx hy ex ey sA sB hxl hyl
  generalize (B + (n + 1) - A) % (n + 1) = u at e1
  generalize (A + (n + 1) - B) % (n + 1) = v at e2
  rcases eq_or_lt_of_le h0 with h | h
  · have e3 : (((n : ℤ) + 1) - (y - x)) % ((n : ℤ) + 1) = 0 := by
      rw [← h, sub_zero, Int.emod_self]
    rw [e3] at e2
    omega
  · have e3 : (((n : ℤ) + 1) - (y - x)) % ((n : ℤ) + 1) = ((n : ℤ) + 1) - (y - x) :=
      Int.emod_eq_of_lt (by linarith) (by linarith)
    rw [e3] at e2
    omega

/-- Positions less than half the cycle apart: the cyclic distance of their reductions is
their distance. -/
theorem w_cdist_red (n : ℕ) (x y : ℤ) (h1 : 2 * (x - y) < (n : ℤ) + 1)
    (h2 : 2 * (y - x) < (n : ℤ) + 1) :
    cdist (w_red n x) (w_red n y) = (x - y).natAbs := by
  rcases le_total x y with h | h
  · rw [w_cdist_red_le n x y (by omega) h2]
    omega
  · rw [cdist_comm, w_cdist_red_le n y x (by omega) h1]
    omega

/-- Lift of a vertex to the window starting at b + 1. -/
def w_lift (n : ℕ) (b : ℤ) (x : Fin (n + 1)) : ℤ :=
  b + 1 + (((x.val : ℤ) - (b + 1)) % ((n : ℤ) + 1))

/-- On the window from b + 1 to b + n + 1, lifting undoes the reduction. -/
theorem w_lift_red (n : ℕ) (b i : ℤ) (h1 : b + 1 ≤ i) (h2 : i ≤ b + ((n : ℤ) + 1)) :
    w_lift n b (w_red n i) = i := by
  unfold w_lift
  rw [w_red_val]
  have ei := Int.mul_ediv_add_emod i ((n : ℤ) + 1)
  have : i % ((n : ℤ) + 1) - (b + 1) =
      (i - (b + 1)) + ((n : ℤ) + 1) * (-(i / ((n : ℤ) + 1))) := by
    linear_combination ei
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- Distance 0 is not in D. -/
theorem w_not_inD_zero (m q : ℕ) (hm : 1 ≤ m) : ¬ inD m q 0 := by
  rintro (⟨h, _⟩ | ⟨j, _, h | h⟩)
  · omega
  · omega
  · omega

/-- Distance 1 is in D. -/
theorem w_inD_one (m q : ℕ) (hm : 1 ≤ m) : inD m q 1 := Or.inl ⟨rfl, by omega⟩

/-- Pigeonhole (step 2 of the proof of Theorem 4.1): of the 2 r + 1 disjoint blocks of L
consecutive positions starting at a - L t for t ≤ 2 r, all inside a range of at most n + 1
positions, one meets no edge of D, since D has at most r edges and so at most 2 r endpoints. -/
theorem w_free_block (n r L : ℕ) (D : Finset (Sym2 (Fin (n + 1)))) (hD : D.card ≤ r)
    (hL : (2 * r + 1) * L ≤ n + 1) (a : ℤ) :
    ∃ t : ℕ, t ≤ 2 * r ∧ ∀ i j : ℤ, a - (L : ℤ) * t ≤ i → i < a - (L : ℤ) * t + L →
      s(w_red n i, w_red n j) ∉ D := by
  classical
  by_contra hcon
  push Not at hcon
  set A : Finset (Fin (n + 1)) := D.biUnion (fun e => e.toFinset) with hA
  have hAc : A.card ≤ 2 * r := by
    have := Finset.card_biUnion_le_card_mul D (fun e => e.toFinset) 2 (by
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega)
    calc A.card ≤ D.card * 2 := this
      _ ≤ 2 * r := by omega
  have hex : ∀ t : ℕ, ∃ i : ℤ,
      (a - (L : ℤ) * t ≤ i ∧ i < a - (L : ℤ) * t + L ∧ w_red n i ∈ A) ∨ 2 * r < t := by
    intro t
    by_cases ht : t ≤ 2 * r
    · obtain ⟨i, j, h1, h2, h3⟩ := hcon t ht
      refine ⟨i, Or.inl ⟨h1, h2, ?_⟩⟩
      rw [hA, Finset.mem_biUnion]
      exact ⟨_, h3, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)⟩
    · exact ⟨0, Or.inr (by omega)⟩
  choose f hf' using hex
  have hf : ∀ t, t ≤ 2 * r →
      a - (L : ℤ) * t ≤ f t ∧ f t < a - (L : ℤ) * t + L ∧ w_red n (f t) ∈ A :=
    fun t ht => (hf' t).resolve_right (by omega)
  have hmaps : Set.MapsTo (fun t => w_red n (f t)) (Finset.range (2 * r + 1) : Set ℕ)
      (A : Set (Fin (n + 1))) := by
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio] at ht
    exact (hf t (by omega)).2.2
  have hinj : Set.InjOn (fun t => w_red n (f t)) (Finset.range (2 * r + 1) : Set ℕ) := by
    intro t1 ht1 t2 ht2 heq
    simp only [Finset.coe_range, Set.mem_Iio] at ht1 ht2
    obtain ⟨a1, b1, -⟩ := hf t1 (by omega)
    obtain ⟨a2, b2, -⟩ := hf t2 (by omega)
    have c1 : (L : ℤ) * t1 ≤ L * (2 * r) := by
      have := Nat.mul_le_mul_left L (show t1 ≤ 2 * r by omega)
      exact_mod_cast this
    have c2 : (L : ℤ) * t2 ≤ L * (2 * r) := by
      have := Nat.mul_le_mul_left L (show t2 ≤ 2 * r by omega)
      exact_mod_cast this
    have hL' : ((2 * r + 1) * L : ℤ) ≤ n + 1 := by exact_mod_cast hL
    have c3 : (0 : ℤ) ≤ L * t1 := by positivity
    have c4 : (0 : ℤ) ≤ L * t2 := by positivity
    have he := w_red_inj n (f t1) (f t2) (by linarith) (by linarith) heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (L : ℤ) * t1 + L ≤ L * t2 := by
        have := Nat.mul_le_mul_left L (show t1 + 1 ≤ t2 by omega)
        have : ((L * (t1 + 1) : ℕ) : ℤ) ≤ ((L * t2 : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at this
        linarith
      linarith
    · have : (L : ℤ) * t2 + L ≤ L * t1 := by
        have := Nat.mul_le_mul_left L (show t2 + 1 ≤ t1 by omega)
        have : ((L * (t2 + 1) : ℕ) : ℤ) ≤ ((L * t1 : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at this
        linarith
      linarith
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at this
  omega

/-- WRAP (Theorem 4.1 for k = 5): deleting at most r edges leaves no proper 4-coloring. -/
theorem edge_robust (r m q : ℕ) (hm : 18 * r + 2 < m) (hq : 24 * r + 12 ≤ q) (h4 : 4 ∣ q)
    (D : Finset (Sym2 (Fin (4 * m * q + 1)))) (hD : D.card ≤ r) :
    ¬ ((G m q).deleteEdges (D : Set _)).Colorable 4 := by
  -- Positions are integers i, read as the vertex w_red (4 m q) i. For each a, a block of 12 m
  -- unaffected positions starts at a - 12 m t with t ≤ 2 r, and LINE applied from that block
  -- gives color(a + 4 m) = color(a). Going q times around in steps of 4 m from an unaffected
  -- position p reaches p + 4 m q, the vertex of p - 1, adjacent to p by an undeleted edge.
  rintro ⟨c⟩
  have hm1 : 1 ≤ m := by omega
  have hmq : m * (24 * r + 12) ≤ m * q := Nat.mul_le_mul_left m hq
  have hmqz : (m : ℤ) * (24 * r + 12) ≤ m * q := by exact_mod_cast hmq
  have hmq0 : (0 : ℤ) ≤ m * q := by positivity
  have hNc : (((4 * m * q : ℕ) : ℤ) + 1) = 4 * (m : ℤ) * q + 1 := by push_cast; ring
  have hmq1 : (1 : ℤ) ≤ m * q := by
    have : 0 < m * q := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hL : (2 * r + 1) * (12 * m) ≤ 4 * m * q + 1 := by linarith [Nat.zero_le (m * q)]
  -- properness of the coloring at two positions within half the cycle
  have hadj : ∀ i j : ℤ, i ≠ j → 2 * (i - j) < 4 * (m : ℤ) * q + 1 →
      2 * (j - i) < 4 * (m : ℤ) * q + 1 → inD m q (i - j).natAbs →
      s(w_red (4 * m * q) i, w_red (4 * m * q) j) ∉ D →
      c (w_red (4 * m * q) i) ≠ c (w_red (4 * m * q) j) := by
    intro i j hij h1 h2 hin hnd
    apply c.valid
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨⟨?_, ?_⟩, fun h => hnd (Finset.mem_coe.mp h)⟩
    · intro he
      exact hij (w_red_inj _ i j (by rw [hNc]; linarith) (by rw [hNc]; linarith) he)
    · rw [w_cdist_red _ i j (by rw [hNc]; linarith) (by rw [hNc]; linarith)]
      exact hin
  -- the coloring of the line is 4m-periodic
  have hper : ∀ a : ℤ, c (w_red (4 * m * q) (a + 4 * m)) = c (w_red (4 * m * q) a) := by
    intro a
    obtain ⟨t, ht, hfree⟩ := w_free_block (4 * m * q) r (12 * m) D hD hL a
    have hmt : (m : ℤ) * t ≤ m * (2 * r) := by
      have := Nat.mul_le_mul_left m ht
      exact_mod_cast this
    have hmt0 : (0 : ℤ) ≤ m * t := by positivity
    refine line_periodic r m q hm hq h4 (fun i => c (w_red (4 * m * q) i))
      (fun i j => s(w_red (4 * m * q) i, w_red (4 * m * q) j) ∈ D) (a - 12 * m * t - 1)
      ?_ ?_ ?_ ?_ a ?_ ?_
    · intro i j h
      rw [Sym2.eq_swap]
      exact h
    · refine ⟨D.image (Sym2.map (w_lift (4 * m * q) (a - 12 * m * t - 1))),
        Finset.card_image_le.trans hD, ?_⟩
      intro i j hi1 hi2 hj1 hj2 hdel
      apply Finset.mem_image.mpr
      refine ⟨_, hdel, ?_⟩
      rw [Sym2.map_mk, w_lift_red _ _ i hi1 (by rw [hNc]; linarith),
        w_lift_red _ _ j hj1 (by rw [hNc]; linarith)]
    · intro i j hi1 hi2 hj1 hj2 hin hnd
      have hij : i ≠ j := by
        rintro rfl
        rw [sub_self, Int.natAbs_zero] at hin
        exact w_not_inD_zero m q hm1 hin
      exact hadj i j hij (by linarith) (by linarith) hin hnd
    · rintro i j hdel ⟨h1, h2⟩
      exact hfree i j (by push_cast; linarith) (by push_cast; linarith) hdel
    · linarith
    · linarith
  -- an unaffected position
  obtain ⟨t0, ht0, hfree0⟩ := w_free_block (4 * m * q) r (12 * m) D hD hL 0
  have hpfree : ∀ j, s(w_red (4 * m * q) (0 - ((12 * m : ℕ) : ℤ) * t0),
      w_red (4 * m * q) j) ∉ D := fun j =>
    hfree0 _ j le_rfl (by push_cast; linarith)
  generalize 0 - ((12 * m : ℕ) : ℤ) * t0 = p at hpfree
  -- walking around the cycle in steps of 4m
  have hchain : ∀ k : ℕ, c (w_red (4 * m * q) (p + 4 * m * k)) = c (w_red (4 * m * q) p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih]
      have : p + 4 * (m : ℤ) * ((k + 1 : ℕ) : ℤ) = (p + 4 * m * k) + 4 * m := by
        push_cast
        ring
      rw [this]
      exact hper _
  have hwrap : w_red (4 * m * q) (p + 4 * m * q) = w_red (4 * m * q) (p - 1) := by
    have : p + 4 * (m : ℤ) * q = (p - 1) + (((4 * m * q : ℕ) : ℤ) + 1) := by
      push_cast
      ring
    rw [this, w_red_add]
  have h1 := hchain q
  rw [hwrap] at h1
  have hin1 : inD m q (p - (p - 1)).natAbs := by
    rw [sub_sub_cancel, Int.natAbs_one]
    exact w_inD_one m q hm1
  exact hadj p (p - 1) (by omega) (by linarith) (by linarith) hin1 (hpfree _) h1.symm

theorem h2_proof : OMA.R_Erdos944_erdos_944_R1.H2 := by
  intro r hr
  show ∃ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    (∀ v, ∃ c : {x : Fin (n + 1) // x ≠ v} → Fin 4, ∀ x y, G.Adj x.val y.val → c x ≠ c y) ∧
    ∀ D : Finset (Sym2 (Fin (n + 1))), D.card ≤ r → ¬ (G.deleteEdges (D : Set _)).Colorable 4
  refine ⟨4 * (18 * r + 3) * (24 * r + 12), G (18 * r + 3) (24 * r + 12), ?_, ?_⟩
  · intro v
    exact vertex_colorable _ _ (by omega) (by omega) v
  · intro D hD
    exact edge_robust r _ _ (by omega) (by omega) ⟨6 * r + 3, by ring⟩ D hD

end OMA.E944H2Proof

theorem OMA.solution : OMA.R_Erdos944_erdos_944_R1.H2 := OMA.E944H2Proof.h2_proof
