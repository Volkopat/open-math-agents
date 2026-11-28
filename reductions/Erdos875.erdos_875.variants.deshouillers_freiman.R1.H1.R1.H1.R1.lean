import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1
import Mathlib

/-!
# Reduction of the structure step (`H1`) of `Erdos875.erdos_875.variants.deshouillers_freiman.R1.H1.R1`

Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

`H1` (ordering): a large admissible set `A` has a subset `B` with `|A \ B| ≤ |A| / 10^6`, in one
residue class mod `q`, such that every sum of `κ` elements of `B` is smaller than every sum of
`κ + q` elements of `B`. (This follows from Theorem 2 of Deshouillers and Freiman, Israel J.
Math. 92 (1995), as in their second paper, Astérisque 258 (1999), p. 144.)

`H2`: the classical bound `|s^B| ≥ s (|B| - s) + 1` for sums of `s` distinct elements.

`main`: (a) all of `A` is in the class of `B` (else the sums of `B` and their translates by one
element are too many, by `H2`); (b) the ordering property for the top `κ` and the bottom `κ + q`
elements of `B`, `κ ≈ (|B| - q) / 2`, bounds the number of missing terms between the `τ`-th
smallest and the `τ`-th largest element of `B` by about `k (|A \ B| + 3) / (2 τ)`;
(c) a suitable `τ` gives the dense middle block of `A`.
-/

namespace OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1_H1_R1

open Finset

/-- Ordering property of large admissible sets. -/
def H1 : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    Erdos875.IsAdmissible (A : Set ℕ) → 4 * N ≤ A.card * (A.card + 3) →
    ∃ q : ℕ, 1 ≤ q ∧ ∃ B : Finset ℕ, B ⊆ A ∧ 10 ^ 6 * (A.card - B.card) ≤ A.card ∧
      (∀ a ∈ B, ∀ b ∈ B, a % q = b % q) ∧
      ∀ κ : ℕ, 1 ≤ κ → κ + q ≤ B.card → ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ B → T₂ ⊆ B →
        T₁.card = κ → T₂.card = κ + q → ∑ x ∈ T₁, x < ∑ x ∈ T₂, x

/-- Lower bound for the number of sums of `r` distinct elements. -/
def H2 : Prop :=
  ∀ (B : Finset ℕ) (r : ℕ), r ≤ B.card →
    r * (B.card - r) + 1 ≤ ((B.powersetCard r).image (fun T => ∑ x ∈ T, x)).card

/-- Increasing enumeration of a finite set of naturals, with the counts below and above. -/
lemma enum (S : Finset ℕ) :
    ∃ e : ℕ → ℕ, (∀ i, i + 1 < S.card → e i < e (i + 1)) ∧ (∀ i, i < S.card → e i ∈ S) ∧
      (∀ z ∈ S, ∃ i, i < S.card ∧ e i = z) ∧
      (∀ i j, i < S.card → j < S.card → (e i < e j ↔ i < j)) ∧
      (∀ i, i < S.card → (S.filter (· < e i)).card = i) ∧
      (∀ i, i < S.card → (S.filter (e i < ·)).card = S.card - 1 - i) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℕ, ∀ i (h : i < S.card), a i = S.orderEmbOfFin rfl ⟨i, h⟩ :=
    ⟨fun i => if h : i < S.card then (S.orderEmbOfFin rfl ⟨i, h⟩ : ℕ) else 0,
      fun i h => by simp [h]⟩
  have hlt : ∀ i j, i < S.card → j < S.card → (a i < a j ↔ i < j) := by
    intro i j hi hj
    rw [hadef i hi, hadef j hj]
    exact (S.orderEmbOfFin rfl).lt_iff_lt
  have hinj : ∀ i, i < S.card → ∀ j, j < S.card → a i = a j → i = j := by
    intro i hi j hj hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := (hlt i j hi hj).mpr h; omega
    · exact h
    · have := (hlt j i hj hi).mpr h; omega
  have hmem : ∀ i, i < S.card → a i ∈ S := by
    intro i hi
    rw [hadef i hi]
    exact Finset.orderEmbOfFin_mem S rfl ⟨i, hi⟩
  have hsurj : ∀ z ∈ S, ∃ i, i < S.card ∧ a i = z := by
    intro z hz
    have hr : z ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hz
    obtain ⟨⟨i, hi⟩, rfl⟩ := hr
    exact ⟨i, hi, hadef i hi⟩
  refine ⟨a, fun i hi => (hlt i (i + 1) (by omega) hi).mpr (Nat.lt_succ_self i), hmem, hsurj,
    hlt, ?_, ?_⟩
  · intro i0 hi0
    have hfx : S.filter (· < a i0) = (Finset.range i0).image a := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨i, hi, rfl⟩ := hsurj z hz1
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr ((hlt i i0 hi hi0).mp hz2), rfl⟩
      · intro hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        have hi' := Finset.mem_range.mp hi
        exact Finset.mem_filter.mpr ⟨hmem i (by omega), (hlt i i0 (by omega) hi0).mpr hi'⟩
    rw [hfx, Finset.card_image_of_injOn (fun i hi j hj hij =>
      hinj i (by have := Finset.mem_range.mp hi; omega) j
        (by have := Finset.mem_range.mp hj; omega) hij), Finset.card_range]
  · intro j0 hj0
    have hfy : S.filter (a j0 < ·) = (Finset.Ico (j0 + 1) S.card).image a := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨i, hi, rfl⟩ := hsurj z hz1
        exact Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨(hlt j0 i hj0 hi).mp hz2, hi⟩, rfl⟩
      · intro hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        have hi' := Finset.mem_Ico.mp hi
        exact Finset.mem_filter.mpr ⟨hmem i hi'.2, (hlt j0 i hj0 hi'.2).mpr (by omega)⟩
    rw [hfy, Finset.card_image_of_injOn (fun i hi j hj hij =>
      hinj i (Finset.mem_Ico.mp hi).2 j (Finset.mem_Ico.mp hj).2 hij), Nat.card_Ico]
    omega

/-- Sums of elements of one residue class. -/
lemma sum_mod {q β : ℕ} {T : Finset ℕ} (h : ∀ x ∈ T, x % q = β % q) :
    (∑ x ∈ T, x) % q = (T.card * β) % q := by
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, ← Nat.mul_mod_mod,
    Nat.mod_mod]
  rw [Nat.mul_mod_mod]

lemma sumq (m : ℕ) : ∀ t, t ≤ m →
    6 * ∑ s ∈ range t, (s + 1) * (m - (s + 1)) + t * (t + 1) * (2 * t + 1) =
      3 * m * (t * (t + 1)) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have := ih (by omega)
    rw [Finset.sum_range_succ]
    obtain ⟨d, rfl⟩ : ∃ d, m = t + 1 + d := ⟨m - (t + 1), by omega⟩
    rw [show t + 1 + d - (t + 1) = d by omega]
    nlinarith


/-- If an element of `A` is outside the residue class of `B`, the sums of `B` and their
translates by this element are all different: a counting bound. -/
lemma class_count (hH2 : H2) {A B : Finset ℕ} {N q a b0 : ℕ}
    (hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N)
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (hBA : B ⊆ A) (hmod : ∀ x ∈ B, x % q = b0 % q) (ha : a ∈ A) (hab : a % q ≠ b0 % q) :
    2 * ∑ s ∈ range B.card, ((s + 1) * (B.card - (s + 1)) + 1) ≤ (B.card + 1) * N := by
  have haB : a ∉ B := fun h => hab (hmod a h)
  have no_eq : ∀ T T' : Finset ℕ, T ⊆ B → T' ⊆ B → 1 ≤ T.card → 1 ≤ T'.card →
      T.card ≠ T'.card → ∑ x ∈ T, x ≠ ∑ x ∈ T', x :=
    fun T T' hT hT' h1 h2 h3 => hadm T T' (hT.trans hBA) (hT'.trans hBA) h1 h2 h3
  have no_eq_a : ∀ T T' : Finset ℕ, T ⊆ B → T' ⊆ B → 1 ≤ T.card →
      ∑ x ∈ T, x ≠ ∑ x ∈ T', x + a := by
    intro T T' hT hT' h1 heq
    have haT' : a ∉ T' := fun h => haB (hT' h)
    by_cases hc : T.card = T'.card + 1
    · have e1 := sum_mod (T := T) (fun x hx => hmod x (hT hx))
      have e2 := sum_mod (T := T') (fun x hx => hmod x (hT' hx))
      have e3 : (T'.card * b0 + b0) % q = (T'.card * b0 + a) % q := by
        have : (∑ x ∈ T', x + a) % q = (T'.card * b0 + a) % q := Nat.ModEq.add_right a e2
        rw [← this, ← heq, e1, hc]
        ring_nf
      have e4 : b0 % q = a % q := Nat.ModEq.add_left_cancel' (T'.card * b0) e3
      exact hab e4.symm
    · refine hadm T (insert a T') (hT.trans hBA) ?_ h1 ?_ ?_ ?_
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ha
        · exact hBA (hT' hz)
      · rw [Finset.card_insert_of_notMem haT']; omega
      · rw [Finset.card_insert_of_notMem haT']; exact hc
      · rw [Finset.sum_insert haT', heq, Nat.add_comm]
  have hmemS : ∀ (s x : ℕ), x ∈ (B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x) →
      ∃ T : Finset ℕ, T ⊆ B ∧ T.card = s + 1 ∧ ∑ z ∈ T, z = x := by
    intro s x hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨T, h1, h2, rfl⟩
  have hinja : Function.Injective (fun x : ℕ => x + a) := fun x y h => by
    simp only at h; omega
  have hdin : ∀ s, Disjoint ((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x))
      (((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x)).image (fun x => x + a)) := by
    intro s
    refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
    obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s x hx
    obtain ⟨y, hy, hy2⟩ := Finset.mem_image.mp hx2
    obtain ⟨T', hT'1, hT'2, rfl⟩ := hmemS s y hy
    exact no_eq_a T T' hT1 hT'1 (by omega) hy2.symm
  have hVcard : ∀ s, s < B.card → 2 * ((s + 1) * (B.card - (s + 1)) + 1) ≤
      ((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x) ∪
        ((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x)).image (fun x => x + a)).card := by
    intro s hs
    rw [Finset.card_union_of_disjoint (hdin s), Finset.card_image_of_injective _ hinja]
    have := hH2 B (s + 1) (by omega)
    omega
  have hVsub : ∀ s ∈ range B.card,
      (B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x) ∪
        ((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x)).image (fun x => x + a) ⊆
      Finset.Icc 1 ((B.card + 1) * N) := by
    intro s hs x hx
    have hs' := Finset.mem_range.mp hs
    have hbound : ∀ T : Finset ℕ, T ⊆ B → T.card = s + 1 →
        1 ≤ ∑ z ∈ T, z ∧ ∑ z ∈ T, z ≤ B.card * N := by
      intro T hT hc
      obtain ⟨z0, hz0⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
      refine ⟨(hA z0 (hBA (hT hz0))).1.trans
        (Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hz0), ?_⟩
      calc ∑ z ∈ T, z ≤ ∑ _z ∈ T, N := Finset.sum_le_sum fun z hz => (hA z (hBA (hT hz))).2
        _ = T.card * N := by simp
        _ ≤ B.card * N := Nat.mul_le_mul_right N (by omega)
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s x hx
      have := hbound T hT1 hT2
      exact Finset.mem_Icc.mpr ⟨this.1, by nlinarith [this.2]⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s y hy
      have := hbound T hT1 hT2
      have haN := (hA a ha).2
      exact Finset.mem_Icc.mpr ⟨by omega, by nlinarith [this.2]⟩
  have hdisj : (range B.card : Set ℕ).PairwiseDisjoint (fun s =>
      (B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x) ∪
        ((B.powersetCard (s + 1)).image (fun T => ∑ x ∈ T, x)).image (fun x => x + a)) := by
    intro s _ s' _ hss
    refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hx2 with hx2 | hx2
    · obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s x hx
      obtain ⟨T', hT'1, hT'2, hT'3⟩ := hmemS s' _ hx2
      exact no_eq T' T hT'1 hT1 (by omega) (by omega) (by omega) hT'3
    · obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s x hx
      obtain ⟨y, hy, hy2⟩ := Finset.mem_image.mp hx2
      obtain ⟨T', hT'1, hT'2, rfl⟩ := hmemS s' y hy
      exact no_eq_a T T' hT1 hT'1 (by omega) hy2.symm
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s y hy
      obtain ⟨T', hT'1, hT'2, hT'3⟩ := hmemS s' _ hx2
      exact no_eq_a T' T hT'1 hT1 (by omega) hT'3
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨T, hT1, hT2, rfl⟩ := hmemS s y hy
      obtain ⟨y', hy', hy2⟩ := Finset.mem_image.mp hx2
      obtain ⟨T', hT'1, hT'2, rfl⟩ := hmemS s' y' hy'
      exact no_eq T' T hT'1 hT1 (by omega) (by omega) (by omega) (hinja hy2)
  have hbi := Finset.card_le_card (Finset.biUnion_subset.mpr hVsub)
  rw [Finset.card_biUnion hdisj, Nat.card_Icc] at hbi
  calc 2 * ∑ s ∈ range B.card, ((s + 1) * (B.card - (s + 1)) + 1)
      = ∑ s ∈ range B.card, 2 * ((s + 1) * (B.card - (s + 1)) + 1) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun s hs => hVcard s (Finset.mem_range.mp hs)
    _ ≤ (B.card + 1) * N := by omega


lemma growq {n q : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < n → b i + q ≤ b (i + 1)) :
    ∀ i j, i ≤ j → j < n → b i + q * (j - i) ≤ b j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hb j hj
    have h3 : j + 1 - i = (j - i) + 1 := by omega
    rw [h3, Nat.mul_add, Nat.mul_one]
    omega

lemma sum_id (q : ℕ) : 2 * ∑ l ∈ range q, (q - 1 - l) + q = q * q := by
  have h1 := Finset.sum_range_reflect (fun l => l) q
  have h2 := Finset.sum_range_id_mul_two q
  rw [h1]
  rcases q with _ | q
  · simp
  · have : (q + 1) * (q + 1 - 1) = q * q + q := by simp; ring
    rw [this] at h2
    nlinarith

lemma alg2 (τ' κ' q θ c N Wd R k : ℕ) (hθ : θ ≤ 1) (hR : 2 * R + q = q * q)
    (hk : k = 2 * (τ' + 1 + κ') + q + θ + c)
    (h1 : κ' * (κ' + q + θ) + (τ' + 1) * (Wd + τ') + q * (τ' + 1 + κ' + θ) + R < N)
    (h4N : 4 * N ≤ k * (k + 3)) :
    4 * ((τ' + 1) * (Wd - (2 * κ' + q + θ + 1))) ≤ 2 * (k * c) + 5 * k := by
  rcases Nat.le_total Wd (2 * κ' + q + θ + 1) with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    have hθ2 : θ * θ ≤ 1 := by
      have : θ = 0 ∨ θ = 1 := by omega
      rcases this with rfl | rfl <;> simp
    subst hk
    nlinarith [Nat.zero_le (q * κ'), Nat.zero_le (q * τ'), Nat.zero_le (c * c),
      Nat.zero_le (c * κ'), Nat.zero_le (c * τ'), Nat.zero_le (c * q), Nat.zero_le (q * θ),
      Nat.zero_le (c * θ)]


/-- The ordering property gives the dense middle block. -/
lemma dense_of_ord (hH2 : H2) {A B : Finset ℕ} {N q : ℕ}
    (hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N)
    (hadm : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x)
    (h4N : 4 * N ≤ A.card * (A.card + 3)) (hk : 10 ^ 8 ≤ A.card) (hq : 1 ≤ q)
    (hBA : B ⊆ A) (hc : 10 ^ 6 * (A.card - B.card) ≤ A.card)
    (hmodB : ∀ a ∈ B, ∀ b ∈ B, a % q = b % q)
    (hord : ∀ κ : ℕ, 1 ≤ κ → κ + q ≤ B.card → ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ B → T₂ ⊆ B →
      T₁.card = κ → T₂.card = κ + q → ∑ x ∈ T₁, x < ∑ x ∈ T₂, x) :
    ∃ u r : ℕ, 100 * u ≤ A.card ∧ 32 * r ≤ u ∧ (∀ a ∈ A, ∀ b ∈ A, a % q = b % q) ∧
      ∃ x ∈ A, ∃ y ∈ A, (A.filter (· < x)).card = u ∧ (A.filter (y < ·)).card = u ∧
        y ≤ x + q * (A.card - 2 * u - 1 + r) := by
  have hmk : B.card ≤ A.card := Finset.card_le_card hBA
  obtain ⟨b, hb1, hbmem, hbsurj, hblt, hbf1, hbf2⟩ := enum B
  obtain ⟨a, ha1, hamem, hasurj, halt, haf1, haf2⟩ := enum A
  set k := A.card with hkdef
  set m := B.card with hmdef
  obtain ⟨m1, hm1⟩ : ∃ m1, m = m1 + 1 := ⟨m - 1, by omega⟩
  have h99 : 99 * k ≤ 100 * m1 := by omega
  have hkk : 10 ^ 8 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hmod0 : ∀ x ∈ B, x % q = b 0 % q := fun x hx => hmodB x hx (b 0) (hbmem 0 (by omega))
  -- (a) all of A is in the class of B
  have hall : ∀ x ∈ A, x % q = b 0 % q := by
    intro x hx
    by_contra hne
    have h1 := class_count hH2 hA hadm hBA hmod0 hx hne
    have h2 := sumq m m le_rfl
    rw [← hmdef] at h1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
    rw [hm1] at h1 h2
    have h3 : (m1 + 2) * ((m1 + 1) * m1) ≤ (m1 + 2) * (3 * N) := by nlinarith
    have h4 := Nat.le_of_mul_le_mul_left h3 (by omega)
    nlinarith
  -- growth of b in steps of q
  have hbstep : ∀ i, i + 1 < m → b i + q ≤ b (i + 1) := by
    intro i hi
    have h1 := hb1 i hi
    have h2 := hmodB (b (i + 1)) (hbmem _ hi) (b i) (hbmem _ (by omega))
    have h3 := Nat.sub_mod_eq_zero_of_mod_eq h2
    have h4 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h3)
    omega
  have hgq := growq hbstep
  have hbN : ∀ i, i < m → b i ≤ N := fun i hi => (hA _ (hBA (hbmem i hi))).2
  have hq3 : 3 * q ≤ k := by
    have h1 := hgq 0 (m - 1) (Nat.zero_le _) (by omega)
    have h2 := hbN (m - 1) (by omega)
    rw [show m - 1 - 0 = m1 by omega] at h1
    by_contra hcon
    have h3 : (k + 1) * m1 ≤ 3 * q * m1 := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  -- parameters
  set c := k - m with hcdef
  obtain ⟨κ, θ, hκ, hθ⟩ : ∃ κ θ, 2 * κ + q + θ = m ∧ θ ≤ 1 :=
    ⟨(m - q) / 2, m - q - 2 * ((m - q) / 2), by omega, by omega⟩
  set r0 := Nat.sqrt (16 * k * (2 * c + 5)) with hr0
  have hr0a : 16 * k * (2 * c + 5) < (r0 + 1) * (r0 + 1) := Nat.lt_succ_sqrt _
  have hr0b : r0 * r0 ≤ 16 * k * (2 * c + 5) := Nat.sqrt_le _
  have hr0c : 150 * r0 ≤ k := by
    by_contra hcon
    have h1 : k + 1 ≤ 150 * r0 := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  obtain ⟨τ', hτ'⟩ : ∃ τ', τ' = 62 * c + 2 + r0 := ⟨_, rfl⟩
  have hτκ : τ' + 1 ≤ κ := by omega
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ = τ' + 1 + κ' := ⟨κ - (τ' + 1), by omega⟩
  have hXτ : 16 * k * (2 * c + 5) < (τ' + 1) * (τ' + 1) :=
    lt_of_lt_of_le hr0a (Nat.mul_le_mul (by omega) (by omega))
  -- the two ends of the middle part of B
  have hres : (b (m - (τ' + 1)) - b τ') % q = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (hmodB _ (hbmem _ (by omega)) _ (hbmem _ (by omega)))
  have hXY := hgq τ' (m - (τ' + 1)) (by omega) (by omega)
  obtain ⟨Wd, hWd⟩ : ∃ Wd, b (m - (τ' + 1)) = b τ' + q * Wd :=
    ⟨(b (m - (τ' + 1)) - b τ') / q, by
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hres)]; omega⟩
  -- the ordering inequality for the top κ and the bottom κ + q
  have hinjb : ∀ i, i < m → ∀ j, j < m → b i = b j → i = j := by
    intro i hi j hj hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := (hblt i j hi hj).mpr h; omega
    · exact h
    · have := (hblt j i hj hi).mpr h; omega
  have himg : ∀ K : Finset ℕ, K ⊆ range m → (K.image b ⊆ B ∧ (K.image b).card = K.card ∧
      ∑ z ∈ K.image b, z = ∑ i ∈ K, b i) := by
    intro K hK
    have hinjK : ∀ i ∈ K, ∀ j ∈ K, b i = b j → i = j := fun i hi j hj hij =>
      hinjb i (Finset.mem_range.mp (hK hi)) j (Finset.mem_range.mp (hK hj)) hij
    refine ⟨?_, Finset.card_image_of_injOn hinjK, Finset.sum_image hinjK⟩
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact hbmem i (Finset.mem_range.mp (hK hi))
  obtain ⟨hT1a, hT1b, hT1c⟩ := himg (Finset.Ico (m - κ) m) (fun i hi =>
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
  obtain ⟨hT2a, hT2b, hT2c⟩ := himg (range (κ + q)) (fun i hi =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
  have hO := hord κ (by omega) (by omega) _ _ hT1a hT2a
    (by rw [hT1b, Nat.card_Ico]; omega) (by rw [hT2b, Finset.card_range])
  rw [hT1c, hT2c, Finset.sum_Ico_eq_sum_range, show m - (m - κ) = κ by omega] at hO
  -- split the sums
  have e1 := Finset.sum_range_add (fun i => b (m - κ + i)) κ' (τ' + 1)
  rw [show κ' + (τ' + 1) = κ by omega] at e1
  have e2 := Finset.sum_range_add b κ q
  have e3 := Finset.sum_range_add b (τ' + 1) κ'
  rw [show τ' + 1 + κ' = κ by omega] at e3
  have t1 : ∑ i ∈ range (τ' + 1), (b i + (q * Wd + q * τ')) ≤
      ∑ i ∈ range (τ' + 1), b (m - κ + (κ' + i)) :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have g1 := hgq i τ' (by omega) (by omega)
      have g2 := hgq (m - (τ' + 1)) (m - κ + (κ' + i)) (by omega) (by omega)
      rw [show m - κ + (κ' + i) - (m - (τ' + 1)) = i by omega] at g2
      have g3 : q * (τ' - i) + q * i = q * τ' := by rw [← Nat.mul_add]; congr 1; omega
      omega
  have t2 : ∑ i ∈ range κ', (b (τ' + 1 + i) + q * (κ' + q + θ)) ≤
      ∑ i ∈ range κ', b (m - κ + i) :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have g1 := hgq (τ' + 1 + i) (m - κ + i) (by omega) (by omega)
      rw [show m - κ + i - (τ' + 1 + i) = κ' + q + θ by omega] at g1
      exact g1
  have t3 : ∑ l ∈ range q, (b (κ + l) + q * ((τ' + 1 + κ' + θ) + (q - 1 - l))) ≤
      ∑ _l ∈ range q, N :=
    Finset.sum_le_sum fun l hl => by
      have hl' := Finset.mem_range.mp hl
      have g1 := hgq (κ + l) (m - 1) (by omega) (by omega)
      rw [show m - 1 - (κ + l) = (τ' + 1 + κ' + θ) + (q - 1 - l) by omega] at g1
      have := hbN (m - 1) (by omega)
      omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at t1 t2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, Finset.card_range, smul_eq_mul, smul_eq_mul] at t3
  have hR := sum_id q
  have hI : q * (κ' * (κ' + q + θ) + (τ' + 1) * (Wd + τ') + q * (τ' + 1 + κ' + θ) +
      ∑ l ∈ range q, (q - 1 - l)) < q * N := by
    have x1 : q * (κ' * (κ' + q + θ) + (τ' + 1) * (Wd + τ') + q * (τ' + 1 + κ' + θ) +
        ∑ l ∈ range q, (q - 1 - l)) =
        κ' * (q * (κ' + q + θ)) + (τ' + 1) * (q * Wd + q * τ') +
          q * (q * (τ' + 1 + κ' + θ) + ∑ l ∈ range q, (q - 1 - l)) := by ring
    rw [x1]
    omega
  have hI' := Nat.lt_of_mul_lt_mul_left hI
  have hkeq : k = 2 * (τ' + 1 + κ') + q + θ + c := by omega
  have hE := alg2 τ' κ' q θ c N Wd _ k hθ hR hkeq hI' h4N
  -- the choice of u and r
  obtain ⟨E, hEdef⟩ : ∃ E, E = Wd - (2 * κ' + q + θ + 1) := ⟨_, rfl⟩
  rw [← hEdef] at hE
  have h64 : 64 * E < τ' + 1 := by
    by_contra hcon
    have h1 : (τ' + 1) * (τ' + 1) ≤ (τ' + 1) * (64 * E) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (τ' + 1) * (64 * E) = 16 * (4 * ((τ' + 1) * E)) := by ring
    have h3 : 16 * k * (2 * c + 5) = 16 * (2 * (k * c) + 5 * k) := by ring
    omega
  refine ⟨τ' + c, E + c, by omega, by omega, fun x hx y hy => by
    rw [hall x hx, hall y hy], a (τ' + c), hamem _ (by omega), a (k - 1 - (τ' + c)),
    hamem _ (by omega), haf1 _ (by omega), ?_, ?_⟩
  · rw [haf2 _ (by omega)]; omega
  · -- a (τ' + c) is not below b τ', and a (k - 1 - (τ' + c)) is not above b (m - (τ' + 1))
    have hsd : (A \ B).card = c := by
      have := Finset.card_sdiff_add_card_eq_card hBA
      omega
    have hlow : b τ' ≤ a (τ' + c) := by
      by_contra hcon
      have hsub : insert (a (τ' + c)) (A.filter (· < a (τ' + c))) ⊆
          B.filter (· < b τ') ∪ (A \ B) := by
        intro z hz
        have hzA : z ∈ A ∧ z < b τ' := by
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact ⟨hamem _ (by omega), by omega⟩
          · have := Finset.mem_filter.mp hz
            exact ⟨this.1, by have := this.2; omega⟩
        by_cases hzB : z ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzB, hzA.2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzA.1, hzB⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (B.filter (· < b τ')) (A \ B)
      rw [Finset.card_insert_of_notMem (by simp), haf1 _ (by omega)] at h1
      rw [hbf1 _ (by omega), hsd] at h2
      omega
    have hhigh : a (k - 1 - (τ' + c)) ≤ b (m - (τ' + 1)) := by
      by_contra hcon
      have hsub : insert (a (k - 1 - (τ' + c))) (A.filter (a (k - 1 - (τ' + c)) < ·)) ⊆
          B.filter (b (m - (τ' + 1)) < ·) ∪ (A \ B) := by
        intro z hz
        have hzA : z ∈ A ∧ b (m - (τ' + 1)) < z := by
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact ⟨hamem _ (by omega), by omega⟩
          · have := Finset.mem_filter.mp hz
            exact ⟨this.1, by have := this.2; omega⟩
        by_cases hzB : z ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzB, hzA.2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzA.1, hzB⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (B.filter (b (m - (τ' + 1)) < ·)) (A \ B)
      rw [Finset.card_insert_of_notMem (by simp), haf2 _ (by omega)] at h1
      rw [hbf2 _ (by omega), hsd] at h2
      omega
    have hW : Wd ≤ k - 2 * (τ' + c) - 1 + (E + c) := by omega
    have := Nat.mul_le_mul_left q hW
    omega

theorem main : H1 → H2 → OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1.H1 := by
  intro hOrd hRS
  obtain ⟨N₀, hN₀⟩ := hOrd
  refine ⟨max N₀ (10 ^ 16), fun N hN A hA hadm h4N => ?_⟩
  have hN1 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 10 ^ 16 ≤ N := le_trans (le_max_right _ _) hN
  have hk : 10 ^ 8 ≤ A.card := by
    by_contra hc
    have h1 : A.card * (A.card + 3) ≤ (10 ^ 8 - 1) * (10 ^ 8 - 1 + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    norm_num at h1 hN2
    omega
  obtain ⟨q, hq, B, hBA, hc, hmodB, hord⟩ := hN₀ N hN1 A hA hadm h4N
  have hA' : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N := fun x hx => hA (Finset.mem_coe.mpr hx)
  have hadmF : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A → 1 ≤ T₁.card → 1 ≤ T₂.card →
      T₁.card ≠ T₂.card → ∑ x ∈ T₁, x ≠ ∑ x ∈ T₂, x := by
    intro T₁ T₂ h1 h2 c1 c2 hne heq
    exact Set.disjoint_left.mp (hadm (show T₁.card ∈ Set.Ici 1 from c1)
      (show T₂.card ∈ Set.Ici 1 from c2) hne)
      ⟨T₁, Finset.coe_subset.mpr h1, rfl, rfl⟩ ⟨T₂, Finset.coe_subset.mpr h2, rfl, heq.symm⟩
  obtain ⟨u, r, hu, hr, hall, x, hx, y, hy, hxc, hyc, hxy⟩ :=
    dense_of_ord hRS hA' hadmF h4N hk hq hBA hc hmodB hord
  exact ⟨q, u, r, hq, hu, hr, hall, x, hx, y, hy, hxc, hyc, hxy⟩

end OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1_H1_R1
