import OMAStatements.S_oeis_a340234
import Mathlib

-- Problem: OEIS A340234, the number of sets of n edges {i, j} (loops allowed) on the labels
-- 0..n-1 whose labels (i + j) mod n are pairwise different. Conjecture: ceiling(n/2)^n for
-- odd n and (n^2/4 + n/2)^(n/2) for even n.
-- Statement: statements/oeis-a340234.lean (declaration OMA.S_oeis_a340234.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Such a set has exactly one edge with each label k < n, so the sets are in bijection
-- with the choice functions k -> F(k), where F(k) is the set of the edges with the label k
-- (lemma a_eq_prod). There are n ordered pairs (i, j) with the label k (j is determined by i).
-- The pairs with i <= j and the pairs with j <= i are exchanged by the swap, and they share
-- the pairs (i, i) with 2 i = k (mod n), so 2 |F(k)| = n + d(k) (lemma two_F). For odd n,
-- d(k) = 1 and |F(k)| = (n+1)/2. For even n, d(k) = 2 for even k and 0 for odd k, so
-- |F(k)| is n/2 + 1 or n/2, and the product is ((n/2 + 1)(n/2))^(n/2).

namespace OMA.A340234

open OMA.S_oeis_a340234 Finset

lemma mod_iff (n x y k : ℕ) (hx : x < n) (hy : y < n) (hk : k < n) :
    (x + y) % n = k ↔ (x + y = k ∨ x + y = k + n) := by
  rcases Nat.lt_or_ge (x + y) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The edges with the label k. -/
def F (n k : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun e => e.1 ≤ e.2 ∧ (e.1 + e.2) % n = k)

/-- All ordered pairs with the label k. -/
def G (n k : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun e => (e.1 + e.2) % n = k)

/-- The number of i with 2 i = k modulo n. -/
def dd (n k : ℕ) : ℕ := ((range n).filter (fun i => (i + i) % n = k)).card

lemma G_card (n k : ℕ) (hk : k < n) : (G n k).card = n := by
  have h : G n k = (range n).image (fun i => (i, if i ≤ k then k - i else k + n - i)) := by
    ext ⟨x, y⟩
    simp only [G, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, hs⟩
      rw [mod_iff n x y k hx hy hk] at hs
      refine ⟨x, hx, rfl, ?_⟩
      split_ifs <;> omega
    · rintro ⟨i, hi, rfl, rfl⟩
      have hlt : (if i ≤ k then k - i else k + n - i) < n := by split_ifs <;> omega
      refine ⟨⟨hi, hlt⟩, ?_⟩
      rw [mod_iff n _ _ k hi hlt hk]
      split_ifs <;> omega
  rw [h, Finset.card_image_of_injective _ (fun i j hij => by simpa using (Prod.mk.inj hij).1),
    Finset.card_range]

lemma two_F (n k : ℕ) (hk : k < n) : 2 * (F n k).card = n + dd n k := by
  have hF : F n k = (G n k).filter (fun e => e.1 ≤ e.2) := by
    ext e
    simp only [F, G, Finset.mem_filter]
    tauto
  set F' := (G n k).filter (fun e => e.2 ≤ e.1) with hF'
  have hswap : F'.card = (F n k).card := by
    rw [hF]
    apply Finset.card_bij (fun e _ => (e.2, e.1))
    · intro e he
      simp only [hF', G, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he ⊢
      refine ⟨⟨⟨he.1.1.2, he.1.1.1⟩, by rw [add_comm]; exact he.1.2⟩, he.2⟩
    · intro e _ e' _ h
      have := Prod.mk.inj h
      exact Prod.ext this.2 this.1
    · intro e he
      simp only [G, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he
      refine ⟨(e.2, e.1), ?_, rfl⟩
      simp only [hF', G, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨⟨he.1.1.2, he.1.1.1⟩, by rw [add_comm]; exact he.1.2⟩, he.2⟩
  have hunion : (G n k).filter (fun e => e.1 ≤ e.2) ∪ F' = G n k := by
    ext e
    simp only [hF', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total e.1 e.2 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
  have hinter : ((G n k).filter (fun e => e.1 ≤ e.2) ∩ F').card = dd n k := by
    unfold dd
    symm
    apply Finset.card_bij (fun i _ => (i, i))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [hF', G, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨⟨hi.1, hi.1⟩, hi.2⟩, le_rfl⟩, ⟨⟨⟨hi.1, hi.1⟩, hi.2⟩, le_rfl⟩⟩
    · intro i _ j _ h
      exact (Prod.mk.inj h).1
    · intro e he
      simp only [hF', G, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he
      have heq : e.1 = e.2 := le_antisymm he.1.2 he.2.2
      refine ⟨e.1, ?_, Prod.ext rfl heq⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨he.1.1.1.1, ?_⟩
      have := he.1.1.2
      rw [← heq] at this
      exact this
  have := Finset.card_union_add_card_inter ((G n k).filter (fun e => e.1 ≤ e.2)) F'
  rw [hunion, hinter, G_card n k hk, hswap, ← hF] at this
  omega

lemma dd_odd (n k : ℕ) (hn : n % 2 = 1) (hk : k < n) : dd n k = 1 := by
  unfold dd
  rw [Finset.card_eq_one]
  refine ⟨if k % 2 = 0 then k / 2 else (k + n) / 2, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hs⟩
    rw [mod_iff n i i k hi hi hk] at hs
    split_ifs <;> omega
  · intro h
    have hi : i < n := by rw [h]; split_ifs <;> omega
    refine ⟨hi, ?_⟩
    rw [mod_iff n i i k hi hi hk, h]
    split_ifs <;> omega

lemma dd_even (n k : ℕ) (hn : n % 2 = 0) (hn0 : 0 < n) (hk : k < n) :
    dd n k = if k % 2 = 0 then 2 else 0 := by
  unfold dd
  split_ifs with hk2
  · have h : (range n).filter (fun i => (i + i) % n = k) = {k / 2, (k + n) / 2} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hs⟩
        rw [mod_iff n i i k hi hi hk] at hs
        omega
      · intro h
        have hi : i < n := by omega
        refine ⟨hi, ?_⟩
        rw [mod_iff n i i k hi hi hk]
        omega
    rw [h, Finset.card_pair (by omega)]
  · rw [Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hi hs
    rw [mod_iff n i i k hi hi hk] at hs
    omega

/-- The set of edges of a choice function. -/
def Phi (n : ℕ) (g : (k : ℕ) → k ∈ range n → ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (range n).attach.image (fun k => g k.1 k.2)

lemma a_eq_prod (n : ℕ) (hn : 0 < n) : a n = ∏ k ∈ range n, (F n k).card := by
  classical
  rw [← Finset.card_pi]
  unfold a
  have sig : ∀ g ∈ Finset.pi (range n) (F n), ∀ k (hk : k ∈ range n),
      (g k hk).1 < n ∧ (g k hk).2 < n ∧ (g k hk).1 ≤ (g k hk).2 ∧ ((g k hk).1 + (g k hk).2) % n = k := by
    intro g hg k hk
    have := Finset.mem_pi.mp hg k hk
    simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have inj : ∀ g ∈ Finset.pi (range n) (F n),
      Function.Injective (fun k : {x // x ∈ range n} => g k.1 k.2) := by
    intro g hg k k' h
    have h1 := (sig g hg k.1 k.2).2.2.2
    have h2 := (sig g hg k'.1 k'.2).2.2.2
    simp only at h
    rw [h] at h1
    exact Subtype.ext (h1.symm.trans h2)
  have hcardPhi : ∀ g ∈ Finset.pi (range n) (F n), (Phi n g).card = n := by
    intro g hg
    unfold Phi
    rw [Finset.card_image_of_injective _ (inj g hg), Finset.card_attach, Finset.card_range]
  have hmem : ∀ g ∈ Finset.pi (range n) (F n), Phi n g ∈ ((range n ×ˢ range n).powerset).filter
      (fun E : Finset (ℕ × ℕ) => (∀ e ∈ E, e.1 ≤ e.2) ∧ E.card = n ∧
        ∀ e ∈ E, ∀ e' ∈ E, (e.1 + e.2) % n = (e'.1 + e'.2) % n → e = e') := by
    intro g hg
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, hcardPhi g hg, ?_⟩
    · intro e he
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
      have := sig g hg k.1 k.2
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr this.1, Finset.mem_range.mpr this.2.1⟩
    · intro e he
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
      exact (sig g hg k.1 k.2).2.2.1
    · intro e he e' he' hs
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp he'
      have h1 := (sig g hg k.1 k.2).2.2.2
      have h2 := (sig g hg k'.1 k'.2).2.2.2
      rw [h1, h2] at hs
      have : k = k' := Subtype.ext hs
      rw [this]
  symm
  apply Finset.card_bij (fun g _ => Phi n g) hmem
  · intro g hg g' hg' h
    funext k hk
    have hin : g k hk ∈ Phi n g' := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_attach _ _, rfl⟩
    obtain ⟨k', _, hk'⟩ := Finset.mem_image.mp hin
    have h1 := (sig g hg k hk).2.2.2
    have h2 := (sig g' hg' k'.1 k'.2).2.2.2
    rw [hk'] at h2
    have hkk : k'.1 = k := h2.symm.trans h1
    obtain ⟨k'', hk''⟩ := k'
    simp only at hkk hk'
    subst hkk
    exact hk'.symm
  · intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    obtain ⟨hsub, hord, hcard, hinj⟩ := hE
    have himg : E.image (fun e => (e.1 + e.2) % n) = range n := by
      apply Finset.eq_of_subset_of_card_le
      · intro k hk
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
      · rw [Finset.card_range, Finset.card_image_of_injOn (fun e he e' he' h => hinj e he e' he' h),
          hcard]
    have hex : ∀ k ∈ range n, ∃ e ∈ E, (e.1 + e.2) % n = k := by
      intro k hk
      rw [← himg] at hk
      obtain ⟨e, he, hs⟩ := Finset.mem_image.mp hk
      exact ⟨e, he, hs⟩
    let g : (k : ℕ) → k ∈ range n → ℕ × ℕ := fun k hk => Classical.choose (hex k hk)
    have hg1 : ∀ k hk, g k hk ∈ E ∧ ((g k hk).1 + (g k hk).2) % n = k :=
      fun k hk => Classical.choose_spec (hex k hk)
    have hgpi : g ∈ Finset.pi (range n) (F n) := by
      rw [Finset.mem_pi]
      intro k hk
      simp only [F, Finset.mem_filter]
      exact ⟨hsub (hg1 k hk).1, hord _ (hg1 k hk).1, (hg1 k hk).2⟩
    refine ⟨g, hgpi, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
      exact (hg1 k.1 k.2).1
    · rw [hcardPhi g hgpi, hcard]

lemma prod_pairs (h : ℕ → ℕ) (m : ℕ) :
    ∏ k ∈ range (2 * m), h k = ∏ j ∈ range m, (h (2 * j) * h (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ]
    ring

theorem result (n : ℕ) (hn : 1 ≤ n) :
    (n % 2 = 1 → a n = ((n + 1) / 2) ^ n) ∧
    (n % 2 = 0 → a n = (n ^ 2 / 4 + n / 2) ^ (n / 2)) := by
  rw [a_eq_prod n (by omega)]
  constructor
  · intro hodd
    have : ∀ k ∈ range n, (F n k).card = (n + 1) / 2 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h1 := two_F n k hk'
      rw [dd_odd n k hodd hk'] at h1
      omega
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range]
  · intro heven
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hc : ∀ k ∈ range (2 * m), (F (2 * m) k).card = if k % 2 = 0 then m + 1 else m := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h1 := two_F (2 * m) k hk'
      rw [dd_even (2 * m) k heven (by omega) hk'] at h1
      split_ifs at h1 ⊢ <;> omega
    rw [Finset.prod_congr rfl hc, prod_pairs]
    have hj : ∀ j ∈ range m, ((if 2 * j % 2 = 0 then m + 1 else m) * (if (2 * j + 1) % 2 = 0 then m + 1 else m))
        = (m + 1) * m := by
      intro j _
      rw [if_pos (by omega), if_neg (by omega)]
    rw [Finset.prod_congr rfl hj, Finset.prod_const, Finset.card_range]
    have e1 : (2 * m) ^ 2 / 4 = m ^ 2 := by
      rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    have e2 : 2 * m / 2 = m := Nat.mul_div_cancel_left _ (by norm_num)
    rw [e1, e2]
    congr 1
    ring

end OMA.A340234

theorem OMA.solution : type_of% @OMA.S_oeis_a340234.main :=
  fun n hn => OMA.A340234.result n hn
