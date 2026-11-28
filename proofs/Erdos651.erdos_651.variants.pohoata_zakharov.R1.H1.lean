import OMAReductions.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1
import Mathlib

/-!
Pohoata–Zakharov, *Convex polytopes from fewer points* (arXiv 2208.04878), Theorem 1.1, in the
form of hypothesis H1: for every t ≥ 2 and all large n, a set of points in general position in
ℝ³ with no n points in convex position has at most t^(C n / t) points.

The proof follows Section 3 of the paper, with constants allowed to depend on t:
* planar positive-fraction Erdős–Szekeres via supersaturation (replacing Pór–Valtr),
* 2-separation via centerpoints (replacing the ham sandwich theorem),
* the above/below Ramsey step done directly on clusters using signed volumes (which replaces
  Propositions 2.5, 2.9 and Corollary 2.6),
* Proposition 3.1 and Proposition 2.3 (cups versus caps for a generic three-facet polyhedron),
* Ramsey on triples and a union of caps.
Draft of the base files by an earlier agent (antigravity / gemini-4-neon); repaired and completed
by claude-code / claude-opus-5-5.
-/

open scoped EuclideanGeometry BigOperators

namespace PZ651

/-! ## Section 1: Finite Partial Orders (Mirsky & Dilworth) -/

def IsChainR {α : Type*} (R : α → α → Prop) (C : Finset α) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, R x y ∨ R y x

def IsAntichainR {α : Type*} (R : α → α → Prop) (A : Finset α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ R x y

lemma isChainR_subset {α : Type*} {R : α → α → Prop} {C₁ C₂ : Finset α}
    (hsub : C₁ ⊆ C₂) (hC : IsChainR R C₂) : IsChainR R C₁ :=
  fun x hx y hy => hC x (hsub hx) y (hsub hy)

lemma isAntichainR_subset {α : Type*} {R : α → α → Prop} {A₁ A₂ : Finset α}
    (hsub : A₁ ⊆ A₂) (hA : IsAntichainR R A₂) : IsAntichainR R A₁ :=
  fun x hx y hy hne => hA x (hsub hx) y (hsub hy) hne

lemma exists_maximal_of_nonempty {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    (S : Finset α) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ y ∈ S, R m y → y = m := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    obtain ⟨x, hx⟩ := hS
    by_cases hm : ∀ y ∈ S, R x y → y = x
    · exact ⟨x, hx, hm⟩
    · push_neg at hm
      obtain ⟨y, hy, hxy, hyx⟩ := hm
      let S' := S.filter (fun z => R y z)
      have hS'sub : S' ⊆ S := Finset.filter_subset _ _
      have hyS' : y ∈ S' := Finset.mem_filter.mpr ⟨hy, hrefl y⟩
      have hxnot : x ∉ S' := by
        intro hx'
        have hyx' : R y x := (Finset.mem_filter.mp hx').2
        exact hyx (hanti y x hyx' hxy)
      have hlt : S'.card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨hS'sub, fun heq => hxnot (heq ▸ hx)⟩)
      obtain ⟨m, hmS', hmax⟩ := ih S'.card hlt S' ⟨y, hyS'⟩ rfl
      have hmS : m ∈ S := hS'sub hmS'
      have hym : R y m := (Finset.mem_filter.mp hmS').2
      refine ⟨m, hmS, fun z hz hmz => hmax z ?_ hmz⟩
      exact Finset.mem_filter.mpr ⟨hz, htrans y m z hym hmz⟩

lemma exists_minimal_of_nonempty {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    (S : Finset α) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ y ∈ S, R y m → y = m :=
  exists_maximal_of_nonempty (R := fun a b => R b a) hrefl
    (fun a b c hab hbc => htrans c b a hbc hab)
    (fun a b hab hba => hanti a b hba hab) S hS

lemma exists_maximal_above {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    (S : Finset α) {x : α} (hx : x ∈ S) :
    ∃ m ∈ S, R x m ∧ ∀ y ∈ S, R m y → y = m := by
  classical
  let U := S.filter (fun z => R x z)
  have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hx, hrefl x⟩
  obtain ⟨m, hmU, hmax⟩ := exists_maximal_of_nonempty hrefl htrans hanti U ⟨x, hxU⟩
  have hmS : m ∈ S := (Finset.mem_filter.mp hmU).1
  have hxm : R x m := (Finset.mem_filter.mp hmU).2
  refine ⟨m, hmS, hxm, fun y hy hmy => hmax y ?_ hmy⟩
  exact Finset.mem_filter.mpr ⟨hy, htrans x m y hxm hmy⟩

lemma chain_exists_top {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    {C : Finset α} (hC : IsChainR R C) (hne : C.Nonempty) :
    ∃ m ∈ C, ∀ x ∈ C, R x m := by
  obtain ⟨m, hm, hmax⟩ := exists_maximal_of_nonempty hrefl htrans hanti C hne
  refine ⟨m, hm, fun x hx => ?_⟩
  rcases hC x hx m hm with hxm | hmx
  · exact hxm
  · rw [hmax x hx hmx]; exact hrefl m

lemma mirsky_cover {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    (k : ℕ) :
    ∀ S : Finset α, (∀ C ⊆ S, IsChainR R C → C.card ≤ k) →
      ∃ ℱ : Finset (Finset α), ℱ.card ≤ k ∧
        (∀ A ∈ ℱ, A ⊆ S ∧ IsAntichainR R A) ∧ S ⊆ ℱ.biUnion id := by
  classical
  induction k with
  | zero =>
    intro S hS
    have hEmpty : S = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := hS {x} (Finset.singleton_subset_iff.mpr hx) (fun a ha b hb => by
        simp only [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact Or.inl (hrefl _))
      simp at h1
    refine ⟨∅, le_rfl, by simp, by simp [hEmpty]⟩
  | succ k ih =>
    intro S hS
    let M := S.filter (fun x => ∀ y ∈ S, R x y → y = x)
    have hMsub : M ⊆ S := Finset.filter_subset _ _
    have hManti : IsAntichainR R M := by
      intro x hx y hy hne hxy
      exact hne ((Finset.mem_filter.mp hx).2 y (hMsub hy) hxy).symm
    let S' := S \ M
    have hS'chains : ∀ C ⊆ S', IsChainR R C → C.card ≤ k := by
      intro C hCsub hCchain
      rcases C.eq_empty_or_nonempty with rfl | hCne
      · simp
      · obtain ⟨top, htopC, htop⟩ := chain_exists_top hrefl htrans hanti hCchain hCne
        have htopS : top ∈ S := (Finset.mem_sdiff.mp (hCsub htopC)).1
        have htopNotM : top ∉ M := (Finset.mem_sdiff.mp (hCsub htopC)).2
        obtain ⟨m, hmS, htopm, hmaxm⟩ := exists_maximal_above hrefl htrans hanti S htopS
        have hmM : m ∈ M := Finset.mem_filter.mpr ⟨hmS, hmaxm⟩
        have hmNotC : m ∉ C := fun hmC => (Finset.mem_sdiff.mp (hCsub hmC)).2 hmM
        have hC'sub : insert m C ⊆ S := Finset.insert_subset hmS (hCsub.trans Finset.sdiff_subset)
        have hC'chain : IsChainR R (insert m C) := by
          intro a ha b hb
          simp only [Finset.mem_insert] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · rw [ha, hb]; exact Or.inl (hrefl _)
          · rw [ha]; exact Or.inr (htrans b top m (htop b hb) htopm)
          · rw [hb]; exact Or.inl (htrans a top m (htop a ha) htopm)
          · exact hCchain a ha b hb
        have hle := hS (insert m C) hC'sub hC'chain
        rw [Finset.card_insert_of_notMem hmNotC] at hle
        omega
    obtain ⟨ℱ', hℱ'card, hℱ'prop, hℱ'cov⟩ := ih S' hS'chains
    refine ⟨insert M ℱ', ?_, ?_, ?_⟩
    · exact (Finset.card_insert_le M ℱ').trans (by omega)
    · intro A hA
      simp only [Finset.mem_insert] at hA
      rcases hA with rfl | hA
      · exact ⟨hMsub, hManti⟩
      · exact ⟨(hℱ'prop A hA).1.trans Finset.sdiff_subset, (hℱ'prop A hA).2⟩
    · intro x hx
      by_cases hxM : x ∈ M
      · exact Finset.mem_biUnion.mpr ⟨M, Finset.mem_insert_self _ _, hxM⟩
      · have hxS' : x ∈ S' := Finset.mem_sdiff.mpr ⟨hx, hxM⟩
        obtain ⟨A, hAℱ', hxA⟩ := Finset.mem_biUnion.mp (hℱ'cov hxS')
        exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_insert_of_mem hAℱ', hxA⟩

lemma mirsky_chain_or_antichain {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hanti : ∀ a b, R a b → R b a → a = b)
    (S : Finset α) (a c : ℕ) (hcard : a * c < S.card) :
    (∃ C ⊆ S, IsChainR R C ∧ c < C.card) ∨
    (∃ A ⊆ S, IsAntichainR R A ∧ a < A.card) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨hC, hA⟩ := h
  obtain ⟨ℱ, hℱcard, hℱprop, hℱcov⟩ := mirsky_cover hrefl htrans hanti c S hC
  have hle : S.card ≤ ℱ.card * a := by
    calc S.card ≤ (ℱ.biUnion id).card := Finset.card_le_card hℱcov
      _ ≤ ∑ A ∈ ℱ, A.card := Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ ℱ, a := Finset.sum_le_sum fun A hAF => hA A (hℱprop A hAF).1 (hℱprop A hAF).2
      _ = ℱ.card * a := by simp
  have hle2 : ℱ.card * a ≤ c * a := Nat.mul_le_mul_right a hℱcard
  have h3 : a * c = c * a := Nat.mul_comm a c
  omega

lemma three_posets_antichain {α : Type*} [DecidableEq α]
    (R : Fin 3 → α → α → Prop)
    (hrefl : ∀ i a, R i a a)
    (htrans : ∀ i a b c, R i a b → R i b c → R i a c)
    (hanti : ∀ i a b, R i a b → R i b a → a = b)
    (S : Finset α)
    (hincomp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i : Fin 3, ¬ R i x y ∧ ¬ R i y x)
    (m : ℕ) (hcard : m ^ 3 < S.card) :
    ∃ i : Fin 3, ∃ A ⊆ S, IsAntichainR (R i) A ∧ m < A.card := by
  classical
  by_contra h
  push_neg at h
  have hpick : ∀ (i : Fin 3) (U : Finset α) (k : ℕ), U ⊆ S → m * k < U.card →
      ∃ C ⊆ U, IsChainR (R i) C ∧ k < C.card := by
    intro i U k hUS hkU
    rcases mirsky_chain_or_antichain (hrefl i) (htrans i) (hanti i) U m k hkU with hC | hA
    · exact hC
    · obtain ⟨A, hAU, hAanti, hAcard⟩ := hA
      exact absurd (h i A (hAU.trans hUS) hAanti) (by omega)
  obtain ⟨C₀, hC₀S, hC₀ch, hC₀card⟩ := hpick 0 S (m ^ 2) (Finset.Subset.refl S) (by rw [show m * m ^ 2 = m ^ 3 by ring]; exact hcard)
  obtain ⟨C₁, hC₁C₀, hC₁ch, hC₁card⟩ := hpick 1 C₀ m hC₀S (by rw [show m * m = m ^ 2 by ring]; exact hC₀card)
  obtain ⟨C₂, hC₂C₁, hC₂ch, hC₂card⟩ := hpick 2 C₁ 1 (hC₁C₀.trans hC₀S) (by omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hC₂card
  have hC₂S : C₂ ⊆ S := hC₂C₁.trans (hC₁C₀.trans hC₀S)
  obtain ⟨i, hi1, hi2⟩ := hincomp x (hC₂S hx) y (hC₂S hy) hxy
  fin_cases i
  · rcases hC₀ch x (hC₁C₀ (hC₂C₁ hx)) y (hC₁C₀ (hC₂C₁ hy)) with h1 | h2
    · exact hi1 h1
    · exact hi2 h2
  · rcases hC₁ch x (hC₂C₁ hx) y (hC₂C₁ hy) with h1 | h2
    · exact hi1 h1
    · exact hi2 h2
  · rcases hC₂ch x hx y hy with h1 | h2
    · exact hi1 h1
    · exact hi2 h2

/-! ## Section 2: Hypergraph Ramsey Theorem -/

lemma ramsey_hypergraph (r : ℕ) :
    ∀ k l : ℕ, ∃ N : ℕ, ∀ (S : Finset ℕ), N ≤ S.card →
      ∀ c : Finset ℕ → Bool,
        (∃ T ⊆ S, T.card = k ∧ ∀ e ⊆ T, e.card = r → c e = true) ∨
        (∃ T ⊆ S, T.card = l ∧ ∀ e ⊆ T, e.card = r → c e = false) := by
  classical
  induction r with
  | zero =>
    intro k l
    refine ⟨max k l, fun S hS c => ?_⟩
    cases hc : c ∅
    · right
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (le_trans (le_max_right k l) hS)
      exact ⟨T, hTS, hTcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
    · left
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (le_trans (le_max_left k l) hS)
      exact ⟨T, hTS, hTcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
  | succ r ihr =>
    intro k l
    suffices h : ∀ s : ℕ, ∀ k l : ℕ, k + l = s →
        ∃ N : ℕ, ∀ (S : Finset ℕ), N ≤ S.card →
          ∀ c : Finset ℕ → Bool,
            (∃ T ⊆ S, T.card = k ∧ ∀ e ⊆ T, e.card = r + 1 → c e = true) ∨
            (∃ T ⊆ S, T.card = l ∧ ∀ e ⊆ T, e.card = r + 1 → c e = false) from h (k + l) k l rfl
    intro s
    induction s with
    | zero =>
      intro k l hkl
      have hk : k = 0 := by omega
      refine ⟨0, fun S _ _ => Or.inl ⟨∅, Finset.empty_subset _, by simp [hk], fun e he hcard => by
        rw [Finset.subset_empty.mp he] at hcard; simp at hcard⟩⟩
    | succ s ihs =>
      intro k l hkl
      by_cases hk : k < r + 1
      · refine ⟨k, fun S hS _ => Or.inl ?_⟩
        obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
        exact ⟨T, hTS, hTcard, fun e he hcard => by
          have := Finset.card_le_card he; omega⟩
      · by_cases hl : l < r + 1
        · refine ⟨l, fun S hS _ => Or.inr ?_⟩
          obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
          exact ⟨T, hTS, hTcard, fun e he hcard => by
            have := Finset.card_le_card he; omega⟩
        · obtain ⟨N₁, hN₁⟩ := ihs (k - 1) l (by omega)
          obtain ⟨N₂, hN₂⟩ := ihs k (l - 1) (by omega)
          obtain ⟨M, hM⟩ := ihr N₁ N₂
          refine ⟨M + 1, fun S hS c => ?_⟩
          have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨x, hxS⟩ := hSne
          let S' := S.erase x
          have hS'card : M ≤ S'.card := by
            rw [Finset.card_erase_of_mem hxS]; omega
          rcases hM S' hS'card (fun e => c (insert x e)) with
            ⟨U, hUS', hUcard, hUtrue⟩ | ⟨U, hUS', hUcard, hUfalse⟩
          · have hxnotU : x ∉ U := fun hxU => (Finset.mem_erase.mp (hUS' hxU)).1 rfl
            rcases hN₁ U (le_of_eq hUcard.symm) c with
              ⟨T, hTU, hTcard, hTtrue⟩ | ⟨T, hTU, hTcard, hTfalse⟩
            · left
              have hxnotT : x ∉ T := fun hxT => hxnotU (hTU hxT)
              refine ⟨insert x T, Finset.insert_subset hxS (hTU.trans (hUS'.trans (Finset.erase_subset x S))), ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hxnotT, hTcard]; omega
              · intro e he hecard
                by_cases hxe : x ∈ e
                · have he'sub : e.erase x ⊆ U := fun y hy => by
                    have hy' := Finset.mem_erase.mp hy
                    have hyT := he hy'.2
                    rcases Finset.mem_insert.mp hyT with rfl | hyT'
                    · exact (hy'.1 rfl).elim
                    · exact hTU hyT'
                  have he'card : (e.erase x).card = r := by
                    rw [Finset.card_erase_of_mem hxe, hecard]; omega
                  have hins : insert x (e.erase x) = e := Finset.insert_erase hxe
                  simpa [hins] using hUtrue (e.erase x) he'sub he'card
                · have heT : e ⊆ T := fun y hy => by
                    rcases Finset.mem_insert.mp (he hy) with rfl | hyT
                    · exact (hxe hy).elim
                    · exact hyT
                  exact hTtrue e heT hecard
            · exact Or.inr ⟨T, hTU.trans (hUS'.trans (Finset.erase_subset x S)), hTcard, hTfalse⟩
          · have hxnotU : x ∉ U := fun hxU => (Finset.mem_erase.mp (hUS' hxU)).1 rfl
            rcases hN₂ U (le_of_eq hUcard.symm) c with
              ⟨T, hTU, hTcard, hTtrue⟩ | ⟨T, hTU, hTcard, hTfalse⟩
            · exact Or.inl ⟨T, hTU.trans (hUS'.trans (Finset.erase_subset x S)), hTcard, hTtrue⟩
            · right
              have hxnotT : x ∉ T := fun hxT => hxnotU (hTU hxT)
              refine ⟨insert x T, Finset.insert_subset hxS (hTU.trans (hUS'.trans (Finset.erase_subset x S))), ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hxnotT, hTcard]; omega
              · intro e he hecard
                by_cases hxe : x ∈ e
                · have he'sub : e.erase x ⊆ U := fun y hy => by
                    have hy' := Finset.mem_erase.mp hy
                    have hyT := he hy'.2
                    rcases Finset.mem_insert.mp hyT with rfl | hyT'
                    · exact (hy'.1 rfl).elim
                    · exact hTU hyT'
                  have he'card : (e.erase x).card = r := by
                    rw [Finset.card_erase_of_mem hxe, hecard]; omega
                  have hins : insert x (e.erase x) = e := Finset.insert_erase hxe
                  simpa [hins] using hUfalse (e.erase x) he'sub he'card
                · have heT : e ⊆ T := fun y hy => by
                    rcases Finset.mem_insert.mp (he hy) with rfl | hyT
                    · exact (hxe hy).elim
                    · exact hyT
                  exact hTfalse e heT hecard

/-! ## Section 3: Radon, Helly, Centerpoint, Kirchberger, Strict Separation -/

lemma radon_theorem {d : ℕ} (S : Finset (ℝ^d)) (hS : d + 2 ≤ S.card) :
    ∃ A B : Finset (ℝ^d), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (convexHull ℝ (A : Set (ℝ^d)) ∩ convexHull ℝ (B : Set (ℝ^d))).Nonempty := by
  classical
  let φ : (↥S → ℝ) →ₗ[ℝ] (ℝ^d × ℝ) :=
    { toFun := fun w => (∑ x : ↥S, w x • x.val, ∑ x : ↥S, w x)
      map_add' := fun u v => by
        ext <;> simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r u => by
        ext <;> simp [mul_smul, Finset.smul_sum, Finset.mul_sum] }
  have hdim_dom : Module.finrank ℝ (↥S → ℝ) = S.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  have hdim_cod : Module.finrank ℝ (ℝ^d × ℝ) = d + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnotinj
  push_neg at hnotinj
  obtain ⟨w, hwker, hwne⟩ := hnotinj
  have hsum_vec : ∑ x : ↥S, w x • x.val = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hwker)
  have hsum_sc : ∑ x : ↥S, w x = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hwker)
  let w' : ℝ^d → ℝ := fun x => if hx : x ∈ S then w ⟨x, hx⟩ else 0
  have hsum_vec' : ∑ x ∈ S, w' x • x = 0 := by
    rw [← Finset.sum_attach S (fun x => w' x • x)]
    convert hsum_vec using 1
    refine Finset.sum_congr rfl fun x _ => by simp [w', x.prop]
  have hsum_sc' : ∑ x ∈ S, w' x = 0 := by
    rw [← Finset.sum_attach S w']
    convert hsum_sc using 1
    refine Finset.sum_congr rfl fun x _ => by simp [w', x.prop]
  let A := S.filter (fun x => 0 < w' x)
  let B := S.filter (fun x => w' x < 0)
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 := (Finset.mem_filter.mp hxA).2
    have h2 := (Finset.mem_filter.mp hxB).2
    linarith
  have hsplit_sc : ∑ x ∈ A, w' x + ∑ x ∈ B, w' x = 0 := by
    rw [← hsum_sc']
    have hsub : A ∪ B ⊆ S := Finset.union_subset hAS hBS
    rw [← Finset.sum_union hdisj]
    exact (Finset.sum_subset hsub fun x hxS hxnot => by
      simp only [Finset.mem_union, A, B, Finset.mem_filter, not_or, not_and] at hxnot
      have h1 : ¬ 0 < w' x := hxnot.1 hxS
      have h2 : ¬ w' x < 0 := hxnot.2 hxS
      exact le_antisymm (not_lt.mp h1) (not_lt.mp h2))
  have hsplit_vec : ∑ x ∈ A, w' x • x + ∑ x ∈ B, w' x • x = 0 := by
    rw [← hsum_vec']
    have hsub : A ∪ B ⊆ S := Finset.union_subset hAS hBS
    rw [← Finset.sum_union hdisj]
    exact (Finset.sum_subset hsub fun x hxS hxnot => by
      simp only [Finset.mem_union, A, B, Finset.mem_filter, not_or, not_and] at hxnot
      have h1 : ¬ 0 < w' x := hxnot.1 hxS
      have h2 : ¬ w' x < 0 := hxnot.2 hxS
      have h0 : w' x = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      simp [h0])
  have hAne : A.Nonempty := by
    by_contra hAemp
    rw [Finset.not_nonempty_iff_eq_empty] at hAemp
    have hBsum : ∑ x ∈ B, w' x = 0 := by simpa [hAemp] using hsplit_sc
    have hBemp : B = ∅ := by
      by_contra hBne
      obtain ⟨y, hyB⟩ := Finset.nonempty_iff_ne_empty.mpr hBne
      have hlt : ∑ x ∈ B, w' x < 0 :=
        Finset.sum_neg (fun x hx => (Finset.mem_filter.mp hx).2) ⟨y, hyB⟩
      linarith
    apply hwne
    ext ⟨x, hx⟩
    have h1 : ¬ 0 < w' x := fun hp => by
      have : x ∈ A := Finset.mem_filter.mpr ⟨hx, hp⟩
      rw [hAemp] at this; exact Finset.notMem_empty _ this
    have h2 : ¬ w' x < 0 := fun hn => by
      have : x ∈ B := Finset.mem_filter.mpr ⟨hx, hn⟩
      rw [hBemp] at this; exact Finset.notMem_empty _ this
    have h0 : w' x = 0 := by linarith
    simpa [w', hx] using h0
  let T : ℝ := ∑ x ∈ A, w' x
  have hTpos : 0 < T := Finset.sum_pos (fun x hx => (Finset.mem_filter.mp hx).2) hAne
  have hBsum : ∑ x ∈ B, (-w' x) = T := by
    rw [Finset.sum_neg_distrib]; linarith
  have hBne : B.Nonempty := by
    by_contra hBemp
    rw [Finset.not_nonempty_iff_eq_empty] at hBemp
    simp [hBemp] at hBsum
    linarith
  let p : ℝ^d := ∑ x ∈ A, (w' x / T) • x
  have hpA : p ∈ convexHull ℝ (A : Set (ℝ^d)) := by
    rw [Finset.convexHull_eq]
    refine ⟨fun x => w' x / T, fun x hx => div_nonneg (le_of_lt (Finset.mem_filter.mp hx).2) hTpos.le,
      ?_, ?_⟩
    · rw [← Finset.sum_div, div_self hTpos.ne']
    · rw [Finset.centerMass_eq_of_sum_1 _ _
        (by rw [← Finset.sum_div, div_self hTpos.ne'] : ∑ x ∈ A, w' x / T = 1)]
      rfl
  have hpB : p ∈ convexHull ℝ (B : Set (ℝ^d)) := by
    rw [Finset.convexHull_eq]
    have hsum1 : ∑ x ∈ B, (-w' x / T) = 1 := by
      rw [← Finset.sum_div, hBsum, div_self hTpos.ne']
    refine ⟨fun x => -w' x / T, fun x hx => div_nonneg (by linarith [(Finset.mem_filter.mp hx).2]) hTpos.le,
      hsum1, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    simp only [id_eq]
    have hneg : ∑ x ∈ B, (-w' x / T) • x = -(T⁻¹ • ∑ x ∈ B, w' x • x) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← neg_smul, smul_smul]; congr 1; ring
    have hpos : p = T⁻¹ • ∑ x ∈ A, w' x • x := by
      simp only [p, Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul]; congr 1; ring
    rw [hneg, hpos]
    have hveq : ∑ x ∈ B, w' x • x = -(∑ x ∈ A, w' x • x) := eq_neg_of_add_eq_zero_right hsplit_vec
    rw [hveq, smul_neg, neg_neg]
  exact ⟨A, B, hAS, hBS, hdisj, hAne, hBne, p, hpA, hpB⟩

lemma helly_theorem {d : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (C : ι → Set (ℝ^d))
    (hC : ∀ i ∈ F, Convex ℝ (C i))
    (hinter : ∀ G ⊆ F, G.card ≤ d + 1 → (⋂ i ∈ G, C i).Nonempty)
    (hF : F.Nonempty) :
    (⋂ i ∈ F, C i).Nonempty := by
  classical
  induction hcard : F.card using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases hle : F.card ≤ d + 1
    · exact hinter F (Finset.Subset.refl _) hle
    · push_neg at hle
      have hstep : ∀ i ∈ F, (⋂ j ∈ F.erase i, C j).Nonempty := fun i hi => by
        have hne : (F.erase i).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hi]; omega)
        have hlt : (F.erase i).card < n := by rw [← hcard, Finset.card_erase_of_mem hi]; omega
        exact ih (F.erase i).card hlt (F.erase i) (fun j hj => hC j (Finset.mem_of_mem_erase hj))
          (fun G hG hGc => hinter G (hG.trans (Finset.erase_subset i F)) hGc) hne rfl
      let p : ι → ℝ^d := fun i => if hi : i ∈ F then (hstep i hi).choose else 0
      have hp_mem : ∀ i ∈ F, ∀ j ∈ F, j ≠ i → p i ∈ C j := fun i hi j hj hji => by
        have hspec := (hstep i hi).choose_spec
        simp only [Set.mem_iInter] at hspec
        simpa [p, hi] using hspec j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      by_cases hinj : Set.InjOn p (F : Set ι)
      · let S := F.image p
        have hScard : d + 2 ≤ S.card := by
          rw [Finset.card_image_of_injOn hinj]; omega
        obtain ⟨A, B, hAS, hBS, hdisj, _, _, q, hqA, hqB⟩ := radon_theorem S hScard
        refine ⟨q, Set.mem_iInter₂.mpr fun j hj => ?_⟩
        by_cases hpjA : p j ∈ A
        · have hpjB : p j ∉ B := Finset.disjoint_left.mp hdisj hpjA
          have hBC : (B : Set (ℝ^d)) ⊆ C j := by
            intro x hx
            obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp (hBS hx)
            have hij : j ≠ i := fun heq => hpjB (heq ▸ hx)
            exact hp_mem i hiF j hj hij
          exact (hC j hj).convexHull_subset_iff.mpr hBC hqB
        · have hAC : (A : Set (ℝ^d)) ⊆ C j := by
            intro x hx
            obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp (hAS hx)
            have hij : j ≠ i := fun heq => hpjA (heq ▸ hx)
            exact hp_mem i hiF j hj hij
          exact (hC j hj).convexHull_subset_iff.mpr hAC hqA
      · unfold Set.InjOn at hinj
        push_neg at hinj
        obtain ⟨i₁, hi₁, i₂, hi₂, heq, hne⟩ := hinj
        refine ⟨p i₁, Set.mem_iInter₂.mpr fun j hj => ?_⟩
        by_cases hji₁ : j = i₁
        · subst hji₁
          rw [heq]
          exact hp_mem i₂ hi₂ j hi₁ hne
        · exact hp_mem i₁ hi₁ j hj hji₁

lemma centerpoint_theorem {d : ℕ} (X : Finset (ℝ^d)) (hX : X.Nonempty) :
    ∃ p : ℝ^d, ∀ (f : (ℝ^d) →ₗ[ℝ] ℝ) (c : ℝ), c ≤ f p →
      X.card ≤ (d + 1) * (X.filter fun x => c ≤ f x).card := by
  classical
  let F := X.powerset.filter (fun Y => d * X.card < (d + 1) * Y.card)
  have hXF : X ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), by
      have hpos : 0 < X.card := Finset.card_pos.mpr hX
      nlinarith⟩
  have hC : ∀ Y ∈ F, Convex ℝ (convexHull ℝ (Y : Set (ℝ^d))) := fun Y _ => convex_convexHull ℝ _
  have hinter : ∀ G ⊆ F, G.card ≤ d + 1 → (⋂ Y ∈ G, convexHull ℝ (Y : Set (ℝ^d))).Nonempty := by
    intro G hGF hGcard
    rcases G.eq_empty_or_nonempty with rfl | hGne
    · exact ⟨0, by simp⟩
    · let bad := G.biUnion (fun Y => X \ Y)
      have hbad_lt : bad.card < X.card := by
        have h1 : (d + 1) * bad.card ≤ ∑ Y ∈ G, (d + 1) * (X \ Y).card := by
          rw [← Finset.mul_sum]
          exact Nat.mul_le_mul_left (d + 1) Finset.card_biUnion_le
        have h2 : ∑ Y ∈ G, (d + 1) * (X \ Y).card < ∑ _Y ∈ G, X.card := by
          refine Finset.sum_lt_sum_of_nonempty hGne fun Y hYG => ?_
          have hYF := Finset.mem_filter.mp (hGF hYG)
          have hYX : Y ⊆ X := Finset.mem_powerset.mp hYF.1
          have hYle : Y.card ≤ X.card := Finset.card_le_card hYX
          have hlt : d * X.card < (d + 1) * Y.card := hYF.2
          have hsd : (X \ Y).card = X.card - Y.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hYX]
          rw [hsd, Nat.mul_sub]
          have e1 : (d + 1) * X.card = d * X.card + X.card := by ring
          exact Nat.sub_lt_left_of_lt_add (Nat.mul_le_mul_left _ hYle) (by linarith)
        simp only [Finset.sum_const, smul_eq_mul] at h2
        have h3 : G.card * X.card ≤ (d + 1) * X.card := Nat.mul_le_mul_right X.card hGcard
        nlinarith
      have hbad_sub : bad ⊆ X := Finset.biUnion_subset.mpr fun _ _ => Finset.sdiff_subset
      have hdiff_ne : (X \ bad).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hXsub : X ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have := Finset.card_le_card hXsub
        omega
      obtain ⟨x, hx⟩ := hdiff_ne
      have hxX := (Finset.mem_sdiff.mp hx).1
      have hxNotBad := (Finset.mem_sdiff.mp hx).2
      refine ⟨x, Set.mem_iInter₂.mpr fun Y hYG => subset_convexHull ℝ (Y : Set (ℝ^d)) ?_⟩
      by_contra hxnotY
      exact hxNotBad (Finset.mem_biUnion.mpr ⟨Y, hYG, Finset.mem_sdiff.mpr ⟨hxX, hxnotY⟩⟩)
  obtain ⟨p, hp⟩ := helly_theorem F (fun Y => convexHull ℝ (Y : Set (ℝ^d))) hC hinter ⟨X, hXF⟩
  refine ⟨p, fun f c hfp => ?_⟩
  by_contra hlt
  push_neg at hlt
  let Y := X.filter (fun x => f x < c)
  have hYsub : Y ⊆ X := Finset.filter_subset _ _
  have hpart : Y.card + (X.filter fun x => c ≤ f x).card = X.card := by
    have hdisj : Disjoint Y (X.filter fun x => c ≤ f x) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      linarith [(Finset.mem_filter.mp hx1).2, (Finset.mem_filter.mp hx2).2]
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext x
    simp only [Finset.mem_union, Y, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx; rcases lt_or_ge (f x) c with h1 | h2
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, h2⟩
  have hYF : Y ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYsub, by nlinarith⟩
  have hpY : p ∈ convexHull ℝ (Y : Set (ℝ^d)) := Set.mem_iInter₂.mp hp Y hYF
  have hconv : Convex ℝ {x : ℝ^d | f x < c} := convex_halfSpace_lt f.isLinear c
  have hYlt : (Y : Set (ℝ^d)) ⊆ {x : ℝ^d | f x < c} := fun x hx => (Finset.mem_filter.mp hx).2
  have hplt : f p < c := hconv.convexHull_subset_iff.mpr hYlt hpY
  linarith

lemma kirchberger_finset {d : ℕ} (A B : Finset (ℝ^d))
    (h : (convexHull ℝ (A : Set (ℝ^d)) ∩ convexHull ℝ (B : Set (ℝ^d))).Nonempty) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, A'.card + B'.card ≤ d + 2 ∧
      (convexHull ℝ (A' : Set (ℝ^d)) ∩ convexHull ℝ (B' : Set (ℝ^d))).Nonempty := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ A' ⊆ A, ∃ B' ⊆ B, A'.card + B'.card = k ∧
      (convexHull ℝ (A' : Set (ℝ^d)) ∩ convexHull ℝ (B' : Set (ℝ^d))).Nonempty
  have hex : ∃ k, P k := ⟨A.card + B.card, A, Finset.Subset.refl _, B, Finset.Subset.refl _, rfl, h⟩
  let k₀ := Nat.find hex
  obtain ⟨A', hA'A, B', hB'B, hcard, p, hpA', hpB'⟩ := Nat.find_spec hex
  have hmin : ∀ A'' ⊆ A, ∀ B'' ⊆ B,
      (convexHull ℝ (A'' : Set (ℝ^d)) ∩ convexHull ℝ (B'' : Set (ℝ^d))).Nonempty →
      k₀ ≤ A''.card + B''.card := fun A'' hA'' B'' hB'' hne =>
    Nat.find_min' hex ⟨A'', hA'', B'', hB'', rfl, hne⟩
  refine ⟨A', hA'A, B', hB'B, ?_, p, hpA', hpB'⟩
  by_contra hgt
  push_neg at hgt
  rw [Finset.convexHull_eq] at hpA' hpB'
  obtain ⟨α, hα_nn, hα_sum, hp_eq_α⟩ := hpA'
  obtain ⟨β, hβ_nn, hβ_sum, hp_eq_β⟩ := hpB'
  rw [Finset.centerMass_eq_of_sum_1 _ _ hα_sum] at hp_eq_α
  rw [Finset.centerMass_eq_of_sum_1 _ _ hβ_sum] at hp_eq_β
  simp only [id_eq] at hp_eq_α hp_eq_β
  have hα_pos : ∀ a ∈ A', 0 < α a := by
    intro a ha
    rcases lt_or_eq_of_le (hα_nn a ha) with hpos | hzero
    · exact hpos
    · exfalso
      have hp_erase : p ∈ convexHull ℝ ((A'.erase a : Finset (ℝ^d)) : Set (ℝ^d)) := by
        rw [Finset.convexHull_eq]
        have hsum' : ∑ x ∈ A'.erase a, α x = 1 := by
          have := Finset.add_sum_erase A' α ha; linarith
        refine ⟨α, fun x hx => hα_nn x (Finset.mem_of_mem_erase hx), hsum', ?_⟩
        rw [Finset.centerMass_eq_of_sum_1 _ _ hsum']
        simp only [id_eq]
        have hvec := Finset.add_sum_erase A' (fun x => α x • x) ha
        rw [← hzero, zero_smul, zero_add] at hvec
        rw [hvec, hp_eq_α]
      have hle := hmin (A'.erase a) ((Finset.erase_subset a A').trans hA'A) B' hB'B
        ⟨p, hp_erase, by
          rw [Finset.convexHull_eq]
          exact ⟨β, hβ_nn, hβ_sum, by rw [Finset.centerMass_eq_of_sum_1 _ _ hβ_sum]; exact hp_eq_β⟩⟩
      rw [Finset.card_erase_of_mem ha] at hle
      have hA'pos : 0 < A'.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
  have hβ_pos : ∀ b ∈ B', 0 < β b := by
    intro b hb
    rcases lt_or_eq_of_le (hβ_nn b hb) with hpos | hzero
    · exact hpos
    · exfalso
      have hp_erase : p ∈ convexHull ℝ ((B'.erase b : Finset (ℝ^d)) : Set (ℝ^d)) := by
        rw [Finset.convexHull_eq]
        have hsum' : ∑ x ∈ B'.erase b, β x = 1 := by
          have := Finset.add_sum_erase B' β hb; linarith
        refine ⟨β, fun x hx => hβ_nn x (Finset.mem_of_mem_erase hx), hsum', ?_⟩
        rw [Finset.centerMass_eq_of_sum_1 _ _ hsum']
        simp only [id_eq]
        have hvec := Finset.add_sum_erase B' (fun x => β x • x) hb
        rw [← hzero, zero_smul, zero_add] at hvec
        rw [hvec, hp_eq_β]
      have hle := hmin A' hA'A (B'.erase b) ((Finset.erase_subset b B').trans hB'B)
        ⟨p, by
          rw [Finset.convexHull_eq]
          exact ⟨α, hα_nn, hα_sum, by rw [Finset.centerMass_eq_of_sum_1 _ _ hα_sum]; exact hp_eq_α⟩,
         hp_erase⟩
      rw [Finset.card_erase_of_mem hb] at hle
      have hB'pos : 0 < B'.card := Finset.card_pos.mpr ⟨b, hb⟩
      omega
  let ψ : ((↥A' → ℝ) × (↥B' → ℝ)) →ₗ[ℝ] (ℝ^d × ℝ × ℝ) :=
    { toFun := fun uv =>
        (∑ a : ↥A', uv.1 a • a.val - ∑ b : ↥B', uv.2 b • b.val,
         ∑ a : ↥A', uv.1 a, ∑ b : ↥B', uv.2 b)
      map_add' := fun x y => by
        ext <;> simp [add_smul, Finset.sum_add_distrib] <;> abel
      map_smul' := fun r x => by
        ext <;> simp [mul_smul, Finset.smul_sum, Finset.mul_sum, smul_sub] }
  have hdim_dom : Module.finrank ℝ ((↥A' → ℝ) × (↥B' → ℝ)) = A'.card + B'.card := by
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_coe]
  have hdim_cod : Module.finrank ℝ (ℝ^d × ℝ × ℝ) = d + 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
  have hnotinj : ¬ Function.Injective ψ := by
    intro hinj
    have := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnotinj
  push_neg at hnotinj
  obtain ⟨⟨u, v⟩, huv_ker, huv_ne⟩ := hnotinj
  have hker := LinearMap.mem_ker.mp huv_ker
  have huv_vec : ∑ a : ↥A', u a • a.val = ∑ b : ↥B', v b • b.val :=
    sub_eq_zero.mp (congrArg Prod.fst hker)
  have hu_sum : ∑ a : ↥A', u a = 0 := congrArg (fun z => z.2.1) hker
  have hv_sum : ∑ b : ↥B', v b = 0 := congrArg (fun z => z.2.2) hker
  -- Since (u, v) ≠ 0 and both sums are 0, there is some negative entry in u or v.
  let negA := Finset.univ.filter (fun a : ↥A' => u a < 0)
  let negB := Finset.univ.filter (fun b : ↥B' => v b < 0)
  have hneg_ne : negA.Nonempty ∨ negB.Nonempty := by
    by_contra hboth
    push_neg at hboth
    have hu_nn : ∀ a : ↥A', 0 ≤ u a := fun a => by
      by_contra hlt; push_neg at hlt
      have : a ∈ negA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      rw [hboth.1] at this; exact Finset.notMem_empty _ this
    have hv_nn : ∀ b : ↥B', 0 ≤ v b := fun b => by
      by_contra hlt; push_neg at hlt
      have : b ∈ negB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      rw [hboth.2] at this; exact Finset.notMem_empty _ this
    have hu0 : ∀ a : ↥A', u a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hu_nn x)).mp hu_sum a (Finset.mem_univ a)
    have hv0 : ∀ b : ↥B', v b = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hv_nn x)).mp hv_sum b (Finset.mem_univ b)
    exact huv_ne (Prod.ext (funext hu0) (funext hv0))
  let ratios : Finset ℝ :=
    negA.image (fun a => α a.val / (-u a)) ∪ negB.image (fun b => β b.val / (-v b))
  have hratios_ne : ratios.Nonempty := by
    rcases hneg_ne with h1 | h2
    · exact Finset.Nonempty.inl (h1.image _)
    · exact Finset.Nonempty.inr (h2.image _)
  let t : ℝ := ratios.min' hratios_ne
  have ht_mem : t ∈ ratios := Finset.min'_mem ratios hratios_ne
  have ht_pos : 0 < t := by
    rcases Finset.mem_union.mp ht_mem with h1 | h2
    · obtain ⟨a, ha, hta⟩ := Finset.mem_image.mp h1
      rw [← hta]
      exact div_pos (hα_pos a.val a.prop) (by linarith [(Finset.mem_filter.mp ha).2])
    · obtain ⟨b, hb, htb⟩ := Finset.mem_image.mp h2
      rw [← htb]
      exact div_pos (hβ_pos b.val b.prop) (by linarith [(Finset.mem_filter.mp hb).2])
  let α' : ℝ^d → ℝ := fun x => if hx : x ∈ A' then α x + t * u ⟨x, hx⟩ else 0
  let β' : ℝ^d → ℝ := fun x => if hx : x ∈ B' then β x + t * v ⟨x, hx⟩ else 0
  have hα'_nn : ∀ a ∈ A', 0 ≤ α' a := fun a ha => by
    simp only [α', ha, dif_pos]
    by_cases hneg : u ⟨a, ha⟩ < 0
    · have hle : t ≤ α a / (-u ⟨a, ha⟩) := Finset.min'_le ratios _
        (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨⟨a, ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩, rfl⟩))
      have hpos : 0 < -u ⟨a, ha⟩ := by linarith
      have hmul := (le_div_iff₀ hpos).mp hle
      linarith
    · nlinarith [hα_pos a ha]
  have hβ'_nn : ∀ b ∈ B', 0 ≤ β' b := fun b hb => by
    simp only [β', hb, dif_pos]
    by_cases hneg : v ⟨b, hb⟩ < 0
    · have hle : t ≤ β b / (-v ⟨b, hb⟩) := Finset.min'_le ratios _
        (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨b, hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩, rfl⟩))
      have hpos : 0 < -v ⟨b, hb⟩ := by linarith
      have hmul := (le_div_iff₀ hpos).mp hle
      linarith
    · nlinarith [hβ_pos b hb]
  have hα'_sum : ∑ a ∈ A', α' a = 1 := by
    rw [← Finset.sum_coe_sort A' α']
    calc ∑ a : ↥A', α' a.val = ∑ a : ↥A', (α a.val + t * u a) :=
          Finset.sum_congr rfl fun a _ => by simp [α', a.prop]
      _ = ∑ a : ↥A', α a.val + t * ∑ a : ↥A', u a := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ a ∈ A', α a + 0 := by rw [Finset.sum_coe_sort A' α, hu_sum, mul_zero]
      _ = 1 := by linarith
  have hβ'_sum : ∑ b ∈ B', β' b = 1 := by
    rw [← Finset.sum_coe_sort B' β']
    calc ∑ b : ↥B', β' b.val = ∑ b : ↥B', (β b.val + t * v b) :=
          Finset.sum_congr rfl fun b _ => by simp [β', b.prop]
      _ = ∑ b : ↥B', β b.val + t * ∑ b : ↥B', v b := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ b ∈ B', β b + 0 := by rw [Finset.sum_coe_sort B' β, hv_sum, mul_zero]
      _ = 1 := by linarith
  have hvec_eq : ∑ a ∈ A', α' a • a = ∑ b ∈ B', β' b • b := by
    have hL : ∑ a ∈ A', α' a • a = p + t • ∑ a : ↥A', u a • a.val := by
      rw [← Finset.sum_coe_sort A' (fun a => α' a • a)]
      calc ∑ a : ↥A', α' a.val • a.val
          = ∑ a : ↥A', (α a.val • a.val + t • (u a • a.val)) :=
            Finset.sum_congr rfl fun a _ => by simp [α', a.prop, add_smul, mul_smul]
        _ = ∑ a : ↥A', α a.val • a.val + t • ∑ a : ↥A', u a • a.val := by
            rw [Finset.sum_add_distrib, Finset.smul_sum]
        _ = p + t • ∑ a : ↥A', u a • a.val := by
            rw [Finset.sum_coe_sort A' (fun a => α a • a), hp_eq_α]
    have hR : ∑ b ∈ B', β' b • b = p + t • ∑ b : ↥B', v b • b.val := by
      rw [← Finset.sum_coe_sort B' (fun b => β' b • b)]
      calc ∑ b : ↥B', β' b.val • b.val
          = ∑ b : ↥B', (β b.val • b.val + t • (v b • b.val)) :=
            Finset.sum_congr rfl fun b _ => by simp [β', b.prop, add_smul, mul_smul]
        _ = ∑ b : ↥B', β b.val • b.val + t • ∑ b : ↥B', v b • b.val := by
            rw [Finset.sum_add_distrib, Finset.smul_sum]
        _ = p + t • ∑ b : ↥B', v b • b.val := by
            rw [Finset.sum_coe_sort B' (fun b => β b • b), hp_eq_β]
    rw [hL, hR, huv_vec]
  let p' : ℝ^d := ∑ a ∈ A', α' a • a
  rcases Finset.mem_union.mp ht_mem with h1 | h2
  · obtain ⟨a₀, ha₀_neg, ht_eq⟩ := Finset.mem_image.mp h1
    have hu_neg : u a₀ < 0 := (Finset.mem_filter.mp ha₀_neg).2
    have hα'0 : α' a₀.val = 0 := by
      simp only [α', a₀.prop, dif_pos]
      rw [← ht_eq]
      have hne' : u a₀ ≠ 0 := by linarith
      beta_reduce
      rw [div_neg, neg_mul, div_mul_cancel₀ _ hne', add_neg_cancel]
    have hp'A : p' ∈ convexHull ℝ ((A'.erase a₀.val : Finset (ℝ^d)) : Set (ℝ^d)) := by
      rw [Finset.convexHull_eq]
      have hsum' : ∑ x ∈ A'.erase a₀.val, α' x = 1 := by
        have := Finset.add_sum_erase A' α' a₀.prop; linarith
      refine ⟨α', fun x hx => hα'_nn x (Finset.mem_of_mem_erase hx), hsum', ?_⟩
      rw [Finset.centerMass_eq_of_sum_1 _ _ hsum']
      simp only [id_eq]
      have := Finset.add_sum_erase A' (fun x => α' x • x) a₀.prop
      rw [hα'0, zero_smul, zero_add] at this
      exact this
    have hp'B : p' ∈ convexHull ℝ (B' : Set (ℝ^d)) := by
      rw [Finset.convexHull_eq]
      refine ⟨β', hβ'_nn, hβ'_sum, ?_⟩
      rw [Finset.centerMass_eq_of_sum_1 _ _ hβ'_sum]
      exact hvec_eq.symm
    have hle := hmin (A'.erase a₀.val) ((Finset.erase_subset _ _).trans hA'A) B' hB'B ⟨p', hp'A, hp'B⟩
    rw [Finset.card_erase_of_mem a₀.prop] at hle
    have hpos : 0 < A'.card := Finset.card_pos.mpr ⟨a₀.val, a₀.prop⟩
    omega
  · obtain ⟨b₀, hb₀_neg, ht_eq⟩ := Finset.mem_image.mp h2
    have hv_neg : v b₀ < 0 := (Finset.mem_filter.mp hb₀_neg).2
    have hβ'0 : β' b₀.val = 0 := by
      simp only [β', b₀.prop, dif_pos]
      rw [← ht_eq]
      have hne' : v b₀ ≠ 0 := by linarith
      beta_reduce
      rw [div_neg, neg_mul, div_mul_cancel₀ _ hne', add_neg_cancel]
    have hp'A : p' ∈ convexHull ℝ (A' : Set (ℝ^d)) := by
      rw [Finset.convexHull_eq]
      exact ⟨α', hα'_nn, hα'_sum, by rw [Finset.centerMass_eq_of_sum_1 _ _ hα'_sum]; rfl⟩
    have hp'B : p' ∈ convexHull ℝ ((B'.erase b₀.val : Finset (ℝ^d)) : Set (ℝ^d)) := by
      rw [Finset.convexHull_eq]
      have hsum' : ∑ x ∈ B'.erase b₀.val, β' x = 1 := by
        have := Finset.add_sum_erase B' β' b₀.prop; linarith
      refine ⟨β', fun x hx => hβ'_nn x (Finset.mem_of_mem_erase hx), hsum', ?_⟩
      rw [Finset.centerMass_eq_of_sum_1 _ _ hsum']
      simp only [id_eq]
      have := Finset.add_sum_erase B' (fun x => β' x • x) b₀.prop
      rw [hβ'0, zero_smul, zero_add] at this
      exact this.trans hvec_eq.symm
    have hle := hmin A' hA'A (B'.erase b₀.val) ((Finset.erase_subset _ _).trans hB'B) ⟨p', hp'A, hp'B⟩
    rw [Finset.card_erase_of_mem b₀.prop] at hle
    have hpos : 0 < B'.card := Finset.card_pos.mpr ⟨b₀.val, b₀.prop⟩
    omega

lemma strict_sep_convexHull_finset {d : ℕ} (A B : Finset (ℝ^d))
    (hdisj : Disjoint (convexHull ℝ (A : Set (ℝ^d))) (convexHull ℝ (B : Set (ℝ^d)))) :
    ∃ (f : (ℝ^d) →ₗ[ℝ] ℝ) (c : ℝ),
      (∀ a ∈ A, c < f a) ∧ (∀ b ∈ B, f b < c) := by
  have hAcomp : IsCompact (convexHull ℝ (A : Set (ℝ^d))) := A.finite_toSet.isCompact_convexHull ℝ
  have hBclosed : IsClosed (convexHull ℝ (B : Set (ℝ^d))) :=
    (B.finite_toSet.isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, v, hAu, huv, hvB⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hAcomp
      (convex_convexHull ℝ _) hBclosed hdisj
  refine ⟨-f.toLinearMap, -(u + v) / 2, fun a ha => ?_, fun b hb => ?_⟩
  · have h1 := hAu a (subset_convexHull ℝ _ ha)
    simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
    linarith
  · have h2 := hvB b (subset_convexHull ℝ _ hb)
    simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
    linarith

end PZ651

open scoped EuclideanGeometry BigOperators

namespace PZ651

/-! ## Section 4: 2D Orientation, Cups-vs-Caps, CCW Ordering, Planar Positive-Fraction ES -/

def orient2 (a b c : ℝ^2) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

lemma orient2_cycle (a b c : ℝ^2) : orient2 a b c = orient2 b c a := by
  unfold orient2; ring

lemma orient2_swap23 (a b c : ℝ^2) : orient2 a c b = -orient2 a b c := by
  unfold orient2; ring

lemma orient2_swap12 (a b c : ℝ^2) : orient2 b a c = -orient2 a b c := by
  unfold orient2; ring

lemma orient2_self_left (a b : ℝ^2) : orient2 a a b = 0 := by
  unfold orient2; ring

lemma orient2_self_right (a b : ℝ^2) : orient2 a b b = 0 := by
  unfold orient2; ring

lemma orient2_self_outer (a b : ℝ^2) : orient2 a b a = 0 := by
  unfold orient2; ring

def IsGP2 (P : Finset (ℝ^2)) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → b ≠ c → a ≠ c → orient2 a b c ≠ 0

def DistinctX2 (P : Finset (ℝ^2)) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a 0 ≠ b 0

lemma isGP2_of_generalPosition {P : Finset (ℝ^2)} (hP : Erdos651.IsInGeneralPosition P) :
    IsGP2 P := by
  intro a ha b hb c hc hab hbc hac hor
  let Y : Finset (ℝ^2) := {a, b, c}
  have hYP : Y ⊆ P := by
    intro x hx
    simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hYcard : Y.card ≤ 2 + 1 := by
    calc Y.card ≤ ({b, c} : Finset (ℝ^2)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
  have hind := hP Y hYP hYcard
  have haY : a ∈ Y := Finset.mem_insert_self _ _
  have hbY : b ∈ Y := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcY : c ∈ Y := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥(Y : Set (ℝ^2)) → ℝ^2)
    ⟨a, haY⟩).mp hind
  let ib : {i : ↥(Y : Set (ℝ^2)) // i ≠ ⟨a, haY⟩} := ⟨⟨b, hbY⟩, fun h => hab (congrArg Subtype.val h).symm⟩
  let ic : {i : ↥(Y : Set (ℝ^2)) // i ≠ ⟨a, haY⟩} := ⟨⟨c, hcY⟩, fun h => hac (congrArg Subtype.val h).symm⟩
  have hibic : ib ≠ ic := fun h => hbc (congrArg (fun z => z.val.val) h)
  -- The vectors b - a and c - a are linearly dependent since orient2 a b c = 0.
  by_cases hbx : b 0 - a 0 = 0
  · by_cases hby : b 1 - a 1 = 0
    · apply hab
      ext k; fin_cases k <;> simp at hbx hby ⊢ <;> linarith
    · have hcx : c 0 - a 0 = 0 := by
        unfold orient2 at hor
        rw [hbx, zero_mul, zero_sub, neg_eq_zero] at hor
        rcases mul_eq_zero.mp hor with h1 | h2
        · exact (hby h1).elim
        · exact h2
      have hcomb : (c 1 - a 1) • (b -ᵥ a) + (-(b 1 - a 1)) • (c -ᵥ a) = 0 := by
        ext k; fin_cases k <;> simp [hbx, hcx] <;> ring
      have h0 := Fintype.linearIndependent_iff.mp hlin
        (fun i => if i = ib then c 1 - a 1 else if i = ic then -(b 1 - a 1) else 0)
      have hsum0 : ∑ i : {i : ↥(Y : Set (ℝ^2)) // i ≠ ⟨a, haY⟩},
          (if i = ib then c 1 - a 1 else if i = ic then -(b 1 - a 1) else 0) •
            (i.val.val -ᵥ a) = 0 := by
        rw [Finset.sum_eq_add ib ic hibic (fun j _ hj => by simp [hj.1, hj.2])
          (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
        simp only [ite_true, hibic.symm, ite_false]
        exact hcomb
      have hcoef := h0 hsum0 ic
      simp only [hibic.symm, ite_false, ite_true, neg_eq_zero] at hcoef
      exact hby hcoef
  · have hcomb : (c 0 - a 0) • (b -ᵥ a) + (-(b 0 - a 0)) • (c -ᵥ a) = 0 := by
      ext k; fin_cases k
      · simp; ring
      · simp; unfold orient2 at hor; linarith
    have h0 := Fintype.linearIndependent_iff.mp hlin
      (fun i => if i = ib then c 0 - a 0 else if i = ic then -(b 0 - a 0) else 0)
    have hsum0 : ∑ i : {i : ↥(Y : Set (ℝ^2)) // i ≠ ⟨a, haY⟩},
        (if i = ib then c 0 - a 0 else if i = ic then -(b 0 - a 0) else 0) •
          (i.val.val -ᵥ a) = 0 := by
      rw [Finset.sum_eq_add ib ic hibic (fun j _ hj => by simp [hj.1, hj.2])
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp only [ite_true, hibic.symm, ite_false]
      exact hcomb
    have hcoef := h0 hsum0 ic
    simp only [hibic.symm, ite_false, ite_true, neg_eq_zero] at hcoef
    exact hbx hcoef

/-- Slope between two points in `ℝ^2`. -/
noncomputable def slope2 (a b : ℝ^2) : ℝ := (b 1 - a 1) / (b 0 - a 0)

lemma orient2_pos_iff_slope_lt {a b c : ℝ^2} (hab : a 0 < b 0) (hbc : b 0 < c 0) :
    0 < orient2 a b c ↔ slope2 a b < slope2 b c := by
  have h1 : 0 < b 0 - a 0 := sub_pos.mpr hab
  have h2 : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hmul : 0 < (b 0 - a 0) * (c 0 - b 0) := mul_pos h1 h2
  rw [slope2, slope2, div_lt_div_iff₀ h1 h2]
  have hid : orient2 a b c = (b 0 - a 0) * (c 1 - b 1) - (b 1 - a 1) * (c 0 - b 0) := by
    unfold orient2; ring
  rw [hid]
  constructor <;> intro h <;> linarith

lemma orient2_neg_iff_slope_gt {a b c : ℝ^2} (hab : a 0 < b 0) (hbc : b 0 < c 0) :
    orient2 a b c < 0 ↔ slope2 b c < slope2 a b := by
  have h1 : 0 < b 0 - a 0 := sub_pos.mpr hab
  have h2 : 0 < c 0 - b 0 := sub_pos.mpr hbc
  rw [slope2, slope2, div_lt_div_iff₀ h2 h1]
  have hid : orient2 a b c = (b 0 - a 0) * (c 1 - b 1) - (b 1 - a 1) * (c 0 - b 0) := by
    unfold orient2; ring
  rw [hid]
  constructor <;> intro h <;> linarith

def IsCup2 (l : List (ℝ^2)) : Prop :=
  (∀ i j (hi : i < l.length) (hj : j < l.length), i < j → (l[i]) 0 < (l[j]) 0) ∧
  (∀ i (hi : i + 2 < l.length), 0 < orient2 l[i] l[i + 1] l[i + 2])

def IsCap2 (l : List (ℝ^2)) : Prop :=
  (∀ i j (hi : i < l.length) (hj : j < l.length), i < j → (l[i]) 0 < (l[j]) 0) ∧
  (∀ i (hi : i + 2 < l.length), orient2 l[i] l[i + 1] l[i + 2] < 0)

lemma slope2_weighted_avg {a b c : ℝ^2} (hab : a 0 < b 0) (hbc : b 0 < c 0) :
    slope2 a c = ((b 0 - a 0) * slope2 a b + (c 0 - b 0) * slope2 b c) / (c 0 - a 0) := by
  have h1 : b 0 - a 0 ≠ 0 := (sub_pos.mpr hab).ne'
  have h2 : c 0 - b 0 ≠ 0 := (sub_pos.mpr hbc).ne'
  have h3 : c 0 - a 0 ≠ 0 := (sub_pos.mpr (hab.trans hbc)).ne'
  simp only [slope2]
  field_simp [h1, h2, h3]
  ring

lemma slope2_between_of_lt {a b c : ℝ^2} (hab : a 0 < b 0) (hbc : b 0 < c 0)
    (hsl : slope2 a b < slope2 b c) :
    slope2 a b < slope2 a c ∧ slope2 a c < slope2 b c := by
  rw [slope2_weighted_avg hab hbc]
  have h1 : 0 < b 0 - a 0 := sub_pos.mpr hab
  have h2 : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have h3 : 0 < c 0 - a 0 := sub_pos.mpr (hab.trans hbc)
  constructor
  · rw [lt_div_iff₀ h3]; nlinarith
  · rw [div_lt_iff₀ h3]; nlinarith

lemma slope2_between_of_gt {a b c : ℝ^2} (hab : a 0 < b 0) (hbc : b 0 < c 0)
    (hsl : slope2 b c < slope2 a b) :
    slope2 b c < slope2 a c ∧ slope2 a c < slope2 a b := by
  rw [slope2_weighted_avg hab hbc]
  have h1 : 0 < b 0 - a 0 := sub_pos.mpr hab
  have h2 : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have h3 : 0 < c 0 - a 0 := sub_pos.mpr (hab.trans hbc)
  constructor
  · rw [lt_div_iff₀ h3]; nlinarith
  · rw [div_lt_iff₀ h3]; nlinarith

lemma isCup2_slope_adj_mono {l : List (ℝ^2)} (hl : IsCup2 l)
    {i j : ℕ} (hij : i < j) (hj : j + 1 < l.length) :
    slope2 l[i] l[i + 1] < slope2 l[j] l[j + 1] := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep : slope2 l[j] l[j + 1] < slope2 l[j + 1] l[j + 2] :=
      (orient2_pos_iff_slope_lt (hl.1 j (j + 1) (by omega) (by omega) (by omega))
        (hl.1 (j + 1) (j + 2) (by omega) hj (by omega))).mp (hl.2 j hj)
    by_cases heq : i = j
    · subst heq; exact hstep
    · exact (ih (by omega) (by omega)).trans hstep

lemma isCup2_slope_lt_right {l : List (ℝ^2)} (hl : IsCup2 l)
    {i j : ℕ} (hij : i + 1 < j) (hj : j < l.length) :
    slope2 l[i] l[i + 1] < slope2 l[i] l[j] ∧ slope2 l[i] l[j] < slope2 l[j - 1] l[j] := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases heq : j = i + 1
    · subst heq
      have hstep : slope2 l[i] l[i + 1] < slope2 l[i + 1] l[i + 2] :=
        (orient2_pos_iff_slope_lt (hl.1 i (i + 1) (by omega) (by omega) (by omega))
          (hl.1 (i + 1) (i + 2) (by omega) hj (by omega))).mp (hl.2 i hj)
      simpa using slope2_between_of_lt (hl.1 i (i + 1) (by omega) (by omega) (by omega))
        (hl.1 (i + 1) (i + 2) (by omega) hj (by omega)) hstep
    · obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
      have hadj : slope2 l[j - 1] l[j] < slope2 l[j] l[j + 1] := by
        have hjm : j - 1 + 1 = j := by omega
        have h := isCup2_slope_adj_mono hl (i := j - 1) (j := j) (by omega) hj
        simpa [hjm] using h
      have hlt : slope2 l[i] l[j] < slope2 l[j] l[j + 1] := h2.trans hadj
      have hbet := slope2_between_of_lt (hl.1 i j (by omega) (by omega) (by omega))
        (hl.1 j (j + 1) (by omega) hj (by omega)) hlt
      exact ⟨h1.trans hbet.1, by simpa using hbet.2⟩

lemma isCup2_slope_gt_left {l : List (ℝ^2)} (hl : IsCup2 l)
    {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    slope2 l[i] l[j] ≤ slope2 l[j - 1] l[j] := by
  by_cases h1 : i + 1 = j
  · subst h1; simp
  · exact le_of_lt (isCup2_slope_lt_right hl (by omega) hj).2

lemma isCup2_slope_ge_right {l : List (ℝ^2)} (hl : IsCup2 l)
    {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    slope2 l[i] l[i + 1] ≤ slope2 l[i] l[j] := by
  by_cases h1 : i + 1 = j
  · subst h1; exact le_rfl
  · exact le_of_lt (isCup2_slope_lt_right hl (by omega) hj).1

lemma isCap2_of_neg_y {l : List (ℝ^2)} :
    IsCap2 l ↔ IsCup2 (l.map fun p => !₂[p 0, -p 1]) := by
  constructor <;> intro hl <;> refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map, Matrix.cons_val_zero]
    exact hl.1 i j hi hj hij
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    have h := hl.2 i hi
    unfold orient2 at h ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linarith
  · intro i j hi hj hij
    have h := hl.1 i j (by simpa using hi) (by simpa using hj) hij
    simpa [Matrix.cons_val_zero] using h
  · intro i hi
    have h := hl.2 i (by simpa using hi)
    simp only [List.getElem_map] at h
    unfold orient2 at h ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    linarith

lemma isCup2_nodup {l : List (ℝ^2)} (hl : IsCup2 l) : l.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have := hl.1 i.val j.val i.isLt j.isLt hlt
    simp only at hij; rw [hij] at this; exact lt_irrefl _ this
  · have := hl.1 j.val i.val j.isLt i.isLt hgt
    simp only at hij; rw [hij] at this; exact lt_irrefl _ this

lemma isCup2_convexIndependent {l : List (ℝ^2)} (hl : IsCup2 l) :
    ConvexIndependent ℝ ((↑) : ↥(l.toFinset : Set (ℝ^2)) → ℝ^2) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro x hx hmem
  have hx' : x ∈ l := List.mem_toFinset.mp hx
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hx'
  -- Choose a slope `m` separating l[r] from all other points of l (so all others lie strictly ABOVE).
  have hm_exists : ∃ m : ℝ,
      (∀ i (hi : i < l.length), i < r → slope2 l[i] l[r] < m) ∧
      (∀ j (hj : j < l.length), r < j → m < slope2 l[r] l[j]) := by
    by_cases hr0 : r = 0
    · subst hr0
      by_cases hl1 : 1 < l.length
      · refine ⟨slope2 l[0] l[1] - 1, fun i _ hi => by omega, fun j hj hrj => ?_⟩
        have hle := isCup2_slope_ge_right hl hrj hj
        linarith
      · exact ⟨0, fun _ _ hi => by omega, fun _ hj hrj => by omega⟩
    · by_cases hrl : r + 1 < l.length
      · have hlt : slope2 l[r - 1] l[r] < slope2 l[r] l[r + 1] := by
          have h := isCup2_slope_adj_mono hl (i := r - 1) (j := r) (by omega) hrl
          have hr1 : r - 1 + 1 = r := by omega
          simpa [hr1] using h
        refine ⟨(slope2 l[r - 1] l[r] + slope2 l[r] l[r + 1]) / 2, ?_, ?_⟩
        · intro i hi hir
          have hle := isCup2_slope_gt_left hl hir hr
          linarith
        · intro j hj hrj
          have hle := isCup2_slope_ge_right hl hrj hj
          linarith
      · refine ⟨slope2 l[r - 1] l[r] + 1, fun i hi hir => ?_, fun j hj hrj => by omega⟩
        have hle := isCup2_slope_gt_left hl hir hr
        linarith
  obtain ⟨m, hml, hmr⟩ := hm_exists
  let f : (ℝ^2) →ₗ[ℝ] ℝ :=
    { toFun := fun p => p 1 - m * p 0
      map_add' := fun p q => by simp; ring
      map_smul' := fun c p => by simp; ring }
  let c : ℝ := f l[r]
  have habove : ∀ y ∈ (l.toFinset : Set (ℝ^2)) \ {l[r]}, c < f y := by
    rintro y ⟨hy, hyne⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hy)
    have hjr : j ≠ r := fun heq => hyne (by subst heq; rfl)
    rcases lt_or_gt_of_ne hjr with hlt | hgt
    · have hdx : 0 < l[r] 0 - l[j] 0 := sub_pos.mpr (hl.1 j r hj hr hlt)
      have hsl := hml j hj hlt
      rw [slope2, div_lt_iff₀ hdx] at hsl
      simp only [c, f, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
    · have hdx : 0 < l[j] 0 - l[r] 0 := sub_pos.mpr (hl.1 r j hr hj hgt)
      have hsl := hmr j hj hgt
      rw [slope2, lt_div_iff₀ hdx] at hsl
      simp only [c, f, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
  have hconv : Convex ℝ {p : ℝ^2 | c < f p} := convex_halfSpace_gt f.isLinear c
  have hlt : c < f l[r] := hconv.convexHull_subset_iff.mpr habove hmem
  exact lt_irrefl c hlt

lemma isCap2_convexIndependent {l : List (ℝ^2)} (hl : IsCap2 l) :
    ConvexIndependent ℝ ((↑) : ↥(l.toFinset : Set (ℝ^2)) → ℝ^2) := by
  let T : (ℝ^2) ≃ₗ[ℝ] (ℝ^2) :=
    { toFun := fun p => !₂[p 0, -p 1]
      invFun := fun p => !₂[p 0, -p 1]
      left_inv := fun p => by ext k; fin_cases k <;> simp
      right_inv := fun p => by ext k; fin_cases k <;> simp
      map_add' := fun p q => by ext k; fin_cases k <;> simp; ring
      map_smul' := fun r p => by ext k; fin_cases k <;> simp }
  have hcup : IsCup2 (l.map T) := isCap2_of_neg_y.mp hl
  have hci := isCup2_convexIndependent hcup
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hci ⊢
  intro x hx hmem
  have hTx : T x ∈ ((l.map T).toFinset : Set (ℝ^2)) := by
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨x, List.mem_toFinset.mp hx, rfl⟩
  apply hci (T x) hTx
  have him : T '' ((l.toFinset : Set (ℝ^2)) \ {x}) ⊆ ((l.map T).toFinset : Set (ℝ^2)) \ {T x} := by
    rintro _ ⟨y, ⟨hy, hyne⟩, rfl⟩
    refine ⟨?_, fun heq => hyne (T.injective heq)⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨y, List.mem_toFinset.mp hy, rfl⟩
  refine convexHull_mono him ?_
  have himg := T.toLinearMap.image_convexHull ((l.toFinset : Set (ℝ^2)) \ {x})
  simp only [LinearEquiv.coe_coe] at himg
  rw [← himg]; exact ⟨x, hmem, rfl⟩

lemma isCup2_append_singleton {l : List (ℝ^2)} {r : ℝ^2}
    (hl : IsCup2 l) (hlen : 2 ≤ l.length)
    (hx : (l[l.length - 1]'(by omega)) 0 < r 0)
    (hor : 0 < orient2 (l[l.length - 2]'(by omega)) (l[l.length - 1]'(by omega)) r) :
    IsCup2 (l ++ [r]) := by
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    simp only [List.length_append, List.length_singleton] at hi hj
    by_cases hjl : j < l.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left hjl]
      exact hl.1 i j (by omega) hjl hij
    · have hj_eq : j = l.length := by omega
      subst hj_eq
      rw [List.getElem_append_left (by omega), List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      by_cases hi_last : i = l.length - 1
      · subst hi_last; exact hx
      · exact (hl.1 i (l.length - 1) (by omega) (by omega) (by omega)).trans hx
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : i + 2 < l.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
          List.getElem_append_left hil]
      exact hl.2 i hil
    · have hi_eq : i = l.length - 2 := by omega
      have hi1 : i + 1 = l.length - 1 := by omega
      have hi2 : i + 2 = l.length := by omega
      rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
          List.getElem_append_right (by omega)]
      simp only [hi2, Nat.sub_self, List.getElem_singleton]
      convert hor using 2 <;> (try congr 1) <;> omega

lemma isCap2_cons {q : ℝ^2} {l : List (ℝ^2)}
    (hl : IsCap2 l) (hlen : 2 ≤ l.length)
    (hx : q 0 < (l[0]'(by omega)) 0)
    (hor : orient2 q (l[0]'(by omega)) (l[1]'(by omega)) < 0) :
    IsCap2 (q :: l) := by
  refine ⟨?_, ?_⟩
  · intro i j hi hj hij
    simp only [List.length_cons] at hi hj
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        by_cases hj0 : j' = 0
        · subst hj0; exact hx
        · exact hx.trans (hl.1 0 j' (by omega) (by omega) (by omega))
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.getElem_cons_succ]
        exact hl.1 i' j' (by omega) (by omega) (by omega)
  · intro i hi
    simp only [List.length_cons] at hi
    cases i with
    | zero => simpa using hor
    | succ i' =>
      simp only [List.getElem_cons_succ]
      exact hl.2 i' (by omega)

lemma erdos_szekeres_cups_caps :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ P : Finset (ℝ^2), DistinctX2 P → IsGP2 P →
        Nat.choose (a + b - 4) (a - 2) < P.card →
        (∃ l : List (ℝ^2), l.length = a ∧ (∀ x ∈ l, x ∈ P) ∧ IsCup2 l) ∨
        (∃ l : List (ℝ^2), l.length = b ∧ (∀ x ∈ l, x ∈ P) ∧ IsCap2 l) := by
  classical
  suffices h : ∀ s a b : ℕ, a + b = s → 2 ≤ a → 2 ≤ b →
      ∀ P : Finset (ℝ^2), DistinctX2 P → IsGP2 P →
        Nat.choose (a + b - 4) (a - 2) < P.card →
        (∃ l : List (ℝ^2), l.length = a ∧ (∀ x ∈ l, x ∈ P) ∧ IsCup2 l) ∨
        (∃ l : List (ℝ^2), l.length = b ∧ (∀ x ∈ l, x ∈ P) ∧ IsCap2 l) from
    fun a b ha hb => h (a + b) a b rfl ha hb
  intro s
  induction s with
  | zero => intro a b hsum ha; omega
  | succ s ih =>
    intro a b hsum ha hb P hdx hgp hcard
    by_cases ha2 : a = 2
    · subst ha2
      simp only [Nat.sub_self, Nat.choose_zero_right] at hcard
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
      have hne : p 0 ≠ q 0 := hdx p hp q hq hpq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left
        refine ⟨[p, q], rfl, fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption, ?_, ?_⟩
        · intro i j hi hj hij
          simp only [List.length_cons, List.length_nil] at hi hj
          have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1; simpa using hlt
        · intro i hi; simp at hi
      · left
        refine ⟨[q, p], rfl, fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption, ?_, ?_⟩
        · intro i j hi hj hij
          simp only [List.length_cons, List.length_nil] at hi hj
          have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1; simpa using hgt
        · intro i hi; simp at hi
    · by_cases hb2 : b = 2
      · subst hb2
        have hch : Nat.choose (a + 2 - 4) (a - 2) = 1 := by
          have heq : a + 2 - 4 = a - 2 := by omega
          rw [heq, Nat.choose_self]
        rw [hch] at hcard
        obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
        have hne : p 0 ≠ q 0 := hdx p hp q hq hpq
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · right
          refine ⟨[p, q], rfl, fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption, ?_, ?_⟩
          · intro i j hi hj hij
            simp only [List.length_cons, List.length_nil] at hi hj
            have hi0 : i = 0 := by omega
            have hj1 : j = 1 := by omega
            subst hi0; subst hj1; simpa using hlt
          · intro i hi; simp at hi
        · right
          refine ⟨[q, p], rfl, fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption, ?_, ?_⟩
          · intro i j hi hj hij
            simp only [List.length_cons, List.length_nil] at hi hj
            have hi0 : i = 0 := by omega
            have hj1 : j = 1 := by omega
            subst hi0; subst hj1; simpa using hgt
          · intro i hi; simp at hi
      · have ha3 : 3 ≤ a := by omega
        have hb3 : 3 ≤ b := by omega
        let E := P.filter (fun p => ∃ u : List (ℝ^2), u.length = a - 1 ∧
          (∀ x ∈ u, x ∈ P) ∧ IsCup2 u ∧ u.getLast? = some p)
        have hEP : E ⊆ P := Finset.filter_subset _ _
        have hpascal : Nat.choose (a + b - 4) (a - 2) =
            Nat.choose (a - 1 + b - 4) (a - 3) + Nat.choose (a + (b - 1) - 4) (a - 2) := by
          have h1 : a + b - 4 = (a + b - 5) + 1 := by omega
          have h2 : a - 2 = (a - 3) + 1 := by omega
          have h3 : a - 1 + b - 4 = a + b - 5 := by omega
          have h4 : a + (b - 1) - 4 = a + b - 5 := by omega
          rw [h1, h2, h3, h4, Nat.choose_succ_succ]
        by_cases hEbig : Nat.choose (a + (b - 1) - 4) (a - 2) < E.card
        · have hdxE : DistinctX2 E := fun x hx y hy => hdx x (hEP hx) y (hEP hy)
          have hgpE : IsGP2 E := fun x hx y hy z hz => hgp x (hEP hx) y (hEP hy) z (hEP hz)
          rcases ih a (b - 1) (by omega) ha (by omega) E hdxE hgpE hEbig with
            ⟨l, hlen, hlE, hcup⟩ | ⟨cl, hclen, hcE, hcap⟩
          · exact Or.inl ⟨l, hlen, fun x hx => hEP (hlE x hx), hcup⟩
          · have hc0_mem : cl[0]'(by omega) ∈ E := hcE _ (List.getElem_mem (by omega))
            obtain ⟨u, hulen, huP, hucup, hulast⟩ := (Finset.mem_filter.mp hc0_mem).2
            have hu_last_eq : u[u.length - 1]'(by omega) = cl[0]'(by omega) := by
              rw [List.getLast?_eq_some_getLast (by intro h; simp [h] at hulen; omega)] at hulast
              have := Option.some.inj hulast
              simpa [List.getLast_eq_getElem] using this
            let q := u[u.length - 2]'(by omega)
            let p := cl[0]'(by omega)
            let r := cl[1]'(by omega)
            have hqP : q ∈ P := huP q (List.getElem_mem (by omega))
            have hpP : p ∈ P := hEP hc0_mem
            have hrP : r ∈ P := hEP (hcE r (List.getElem_mem (by omega)))
            have hqp_x : q 0 < p 0 := by
              have := hucup.1 (u.length - 2) (u.length - 1) (by omega) (by omega) (by omega)
              rw [hu_last_eq] at this; exact this
            have hpr_x : p 0 < r 0 := hcap.1 0 1 (by omega) (by omega) (by omega)
            have hqp_ne : q ≠ p := fun h => by rw [h] at hqp_x; exact lt_irrefl _ hqp_x
            have hpr_ne : p ≠ r := fun h => by rw [h] at hpr_x; exact lt_irrefl _ hpr_x
            have hqr_ne : q ≠ r := fun h => by
              have := hqp_x.trans hpr_x; rw [h] at this; exact lt_irrefl _ this
            have hor_ne : orient2 q p r ≠ 0 := hgp q hqP p hpP r hrP hqp_ne hpr_ne hqr_ne
            rcases lt_or_gt_of_ne hor_ne with hneg | hpos
            · right
              refine ⟨q :: cl, by simp [hclen]; omega, fun x hx => ?_, ?_⟩
              · rcases List.mem_cons.mp hx with rfl | hxc
                · exact hqP
                · exact hEP (hcE x hxc)
              · exact isCap2_cons hcap (by omega) hqp_x hneg
            · left
              refine ⟨u ++ [r], by simp [hulen]; omega, fun x hx => ?_, ?_⟩
              · rcases List.mem_append.mp hx with hxu | hxr
                · exact huP x hxu
                · rw [List.mem_singleton.mp hxr]; exact hrP
              · refine isCup2_append_singleton hucup (by omega) ?_ ?_
                · rwa [hu_last_eq]
                · rwa [hu_last_eq]
        · have hPEbig : Nat.choose (a - 1 + b - 4) (a - 3) < (P \ E).card := by
            have hsd : (P \ E).card = P.card - E.card := by
              rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hEP]
            omega
          have hdxPE : DistinctX2 (P \ E) :=
            fun x hx y hy => hdx x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy)
          have hgpPE : IsGP2 (P \ E) :=
            fun x hx y hy z hz => hgp x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy) z (Finset.sdiff_subset hz)
          have hsub3 : a - 1 - 2 = a - 3 := by omega
          rcases ih (a - 1) b (by omega) (by omega) hb (P \ E) hdxPE hgpPE (by simpa [hsub3] using hPEbig) with
            ⟨u, hulen, huPE, hucup⟩ | ⟨c, hclen, hcPE, hcap⟩
          · exfalso
            let p := u[u.length - 1]'(by omega)
            have hpPE : p ∈ P \ E := huPE p (List.getElem_mem (by omega))
            have hpP : p ∈ P := (Finset.mem_sdiff.mp hpPE).1
            have hpNotE : p ∉ E := (Finset.mem_sdiff.mp hpPE).2
            apply hpNotE
            refine Finset.mem_filter.mpr ⟨hpP, u, hulen, fun x hx => (Finset.mem_sdiff.mp (huPE x hx)).1,
              hucup, ?_⟩
            rw [List.getLast?_eq_some_getLast (by intro h; simp [h] at hulen; omega)]
            simp [p, List.getLast_eq_getElem]
          · exact Or.inr ⟨c, hclen, fun x hx => (Finset.mem_sdiff.mp (hcPE x hx)).1, hcap⟩

lemma erdos_szekeres_2d (m : ℕ) (hm : 2 ≤ m) (P : Finset (ℝ^2))
    (hdx : DistinctX2 P) (hgp : IsGP2 P) (hcard : Nat.choose (2 * m - 4) (m - 2) < P.card) :
    Erdos651.HasConvexSubset m P := by
  have h2m : m + m - 4 = 2 * m - 4 := by omega
  rcases erdos_szekeres_cups_caps m m hm hm P hdx hgp (by simpa [h2m] using hcard) with
    ⟨l, hlen, hlP, hcup⟩ | ⟨l, hlen, hlP, hcap⟩
  · refine ⟨l.toFinset, fun x hx => hlP x (List.mem_toFinset.mp hx), ?_,
      isCup2_convexIndependent hcup⟩
    rw [List.toFinset_card_of_nodup (isCup2_nodup hcup), hlen]
  · refine ⟨l.toFinset, fun x hx => hlP x (List.mem_toFinset.mp hx), ?_,
      isCap2_convexIndependent hcap⟩
    have hnodup : l.Nodup := by
      rw [List.nodup_iff_injective_getElem]
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have := hcap.1 i.val j.val i.isLt j.isLt hlt; simp only at hij; rw [hij] at this; exact lt_irrefl _ this
      · have := hcap.1 j.val i.val j.isLt i.isLt hgt; simp only at hij; rw [hij] at this; exact lt_irrefl _ this
    rw [List.toFinset_card_of_nodup hnodup, hlen]

/-- Any convex-independent general-position planar set with distinct x-coords can be ordered CCW. -/
lemma ccw_order_of_convex_gp {P : Finset (ℝ^2)} (hm : 3 ≤ P.card)
    (hdx : DistinctX2 P) (hgp : IsGP2 P)
    (hconv : ConvexIndependent ℝ ((↑) : ↥(P : Set (ℝ^2)) → ℝ^2)) :
    ∃ v : Fin P.card → ℝ^2,
      Function.Injective v ∧ (∀ i, v i ∈ P) ∧
      (∀ i j k : Fin P.card, i < j → j < k → 0 < orient2 (v i) (v j) (v k)) := by
  classical
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₀, hv₀P, hv₀min⟩ := Finset.exists_min_image P (fun p => p 0) hPne
  let rest := P.erase v₀
  have hrest_x : ∀ p ∈ rest, v₀ 0 < p 0 := fun p hp => by
    have hne : p ≠ v₀ := (Finset.mem_erase.mp hp).1
    have hpP : p ∈ P := (Finset.mem_erase.mp hp).2
    have hle := hv₀min p hpP
    have hxne : v₀ 0 ≠ p 0 := hdx v₀ hv₀P p hpP hne.symm
    exact lt_of_le_of_ne hle hxne
  have hslope_inj : Set.InjOn (fun p => slope2 v₀ p) (rest : Set (ℝ^2)) := by
    intro p hp q hq heq
    by_contra hpq
    have hp0 : 0 < p 0 - v₀ 0 := sub_pos.mpr (hrest_x p hp)
    have hq0 : 0 < q 0 - v₀ 0 := sub_pos.mpr (hrest_x q hq)
    simp only [slope2] at heq
    rw [div_eq_div_iff hp0.ne' hq0.ne'] at heq
    have hor0 : orient2 v₀ p q = 0 := by unfold orient2; linarith
    exact hgp v₀ hv₀P p (Finset.mem_erase.mp hp).2 q (Finset.mem_erase.mp hq).2
      (Finset.mem_erase.mp hp).1.symm hpq (Finset.mem_erase.mp hq).1.symm hor0
  let slopes := rest.image (fun p => slope2 v₀ p)
  have hslopes_card : slopes.card = P.card - 1 := by
    rw [Finset.card_image_of_injOn hslope_inj, Finset.card_erase_of_mem hv₀P]
  let e_ord : Fin slopes.card ≃o ↥slopes := slopes.orderIsoOfFin rfl
  let inv_p : ↥slopes → ℝ^2 := fun s => (Finset.mem_image.mp s.prop).choose
  have hinv_mem : ∀ s : ↥slopes, inv_p s ∈ rest := fun s => (Finset.mem_image.mp s.prop).choose_spec.1
  have hinv_sl : ∀ s : ↥slopes, slope2 v₀ (inv_p s) = s.val := fun s =>
    (Finset.mem_image.mp s.prop).choose_spec.2
  let v : Fin P.card → ℝ^2 := fun i =>
    if hi : i.val = 0 then v₀
    else inv_p (e_ord ⟨i.val - 1, by omega⟩)
  have hv_mem : ∀ i, v i ∈ P := fun i => by
    dsimp only [v]
    split_ifs with hi
    · exact hv₀P
    · exact (Finset.mem_erase.mp (hinv_mem _)).2
  have hv_x_gt : ∀ i : Fin P.card, i.val ≠ 0 → v₀ 0 < (v i) 0 := fun i hi => by
    simp only [v, hi, dif_neg, not_false_eq_true]
    exact hrest_x _ (hinv_mem _)
  have hv_slope_mono : ∀ i j : Fin P.card, i.val ≠ 0 → j.val ≠ 0 → i < j →
      slope2 v₀ (v i) < slope2 v₀ (v j) := fun i j hi hj hij => by
    simp only [v, hi, hj, dif_neg, not_false_eq_true, hinv_sl]
    have hlt : (⟨i.val - 1, by omega⟩ : Fin slopes.card) < ⟨j.val - 1, by omega⟩ := by
      simp [Fin.lt_def]; omega
    exact e_ord.strictMono hlt
  have hv_inj : Function.Injective v := by
    intro i j hij
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · exact Fin.ext (by omega)
    · exfalso
      have hgt := hv_x_gt j hj0
      rw [← hij] at hgt
      simp only [v, hi0, dif_pos] at hgt
      exact lt_irrefl _ hgt
    · exfalso
      have hgt := hv_x_gt i hi0
      rw [hij] at hgt
      simp only [v, hj0, dif_pos] at hgt
      exact lt_irrefl _ hgt
    · by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have := hv_slope_mono i j hi0 hj0 hlt; rw [hij] at this; exact lt_irrefl _ this
      · have := hv_slope_mono j i hj0 hi0 hgt; rw [hij] at this; exact lt_irrefl _ this
  have hor0 : ∀ i j : Fin P.card, 0 < i.val → i < j → 0 < orient2 v₀ (v i) (v j) := by
    intro i j hi hij
    have hi0 : i.val ≠ 0 := by omega
    have hj0 : j.val ≠ 0 := by omega
    have hdx1 : 0 < (v i) 0 - v₀ 0 := sub_pos.mpr (hv_x_gt i hi0)
    have hdx2 : 0 < (v j) 0 - v₀ 0 := sub_pos.mpr (hv_x_gt j hj0)
    have hsl := hv_slope_mono i j hi0 hj0 hij
    rw [slope2, slope2, div_lt_div_iff₀ hdx1 hdx2] at hsl
    unfold orient2; linarith
  refine ⟨v, hv_inj, hv_mem, fun i j k hij hjk => ?_⟩
  by_cases hi0 : i.val = 0
  · have hvi : v i = v₀ := by simp [v, hi0]
    rw [hvi]
    exact hor0 j k (by omega) hjk
  · have hj0 : 0 < j.val := by omega
    have hk0 : 0 < k.val := by omega
    have hne : orient2 (v i) (v j) (v k) ≠ 0 :=
      hgp (v i) (hv_mem i) (v j) (hv_mem j) (v k) (hv_mem k)
        (fun h => (ne_of_lt hij) (hv_inj h))
        (fun h => (ne_of_lt hjk) (hv_inj h))
        (fun h => (ne_of_lt (hij.trans hjk)) (hv_inj h))
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exfalso
      -- Barycentric contradiction: v j ∈ convexHull {v₀, v i, v k} ⊆ convexHull (P \ {v j})!
      let Δ := orient2 v₀ (v i) (v k)
      have hΔ : 0 < Δ := hor0 i k (by omega) (hij.trans hjk)
      let c0 := orient2 (v i) (v k) (v j) / Δ
      let ci := orient2 (v k) v₀ (v j) / Δ
      let ck := orient2 v₀ (v i) (v j) / Δ
      have hc0 : 0 < c0 := div_pos (by rw [orient2_swap23]; linarith) hΔ
      have hci : 0 < ci := div_pos (by rw [orient2_cycle]; exact hor0 j k hj0 hjk) hΔ
      have hck : 0 < ck := div_pos (hor0 i j (by omega) hij) hΔ
      have hsum1 : c0 + ci + ck = 1 := by
        dsimp only [c0, ci, ck, Δ]
        have hnum : orient2 (v i) (v k) (v j) + orient2 (v k) v₀ (v j) +
            orient2 v₀ (v i) (v j) = orient2 v₀ (v i) (v k) := by unfold orient2; ring
        rw [← add_div, ← add_div, hnum, div_self hΔ.ne']
      have hvec : c0 • v₀ + ci • v i + ck • v k = v j := by
        ext coord
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, c0, ci, ck]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          ← add_div, div_eq_iff hΔ.ne']
        dsimp only [Δ]
        fin_cases coord <;> (unfold orient2; simp; ring)
      have hv₀_ne : v₀ ≠ v j := fun h => by
        have := hv_x_gt j (by omega); rw [← h] at this; exact lt_irrefl _ this
      have hvi_ne : v i ≠ v j := fun h => (ne_of_lt hij) (hv_inj h)
      have hvk_ne : v k ≠ v j := fun h => (ne_of_gt hjk) (hv_inj h)
      have hmem_sdiff : v j ∈ convexHull ℝ ((P : Set (ℝ^2)) \ {v j}) := by
        have hsub : ({v₀, v i, v k} : Set (ℝ^2)) ⊆ (P : Set (ℝ^2)) \ {v j} := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact ⟨hv₀P, hv₀_ne⟩
          · exact ⟨hv_mem i, hvi_ne⟩
          · exact ⟨hv_mem k, hvk_ne⟩
        apply convexHull_mono hsub
        have hv0c : v₀ ∈ convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2)) :=
          subset_convexHull ℝ _ (by simp)
        have hvic : v i ∈ convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2)) :=
          subset_convexHull ℝ _ (by simp)
        have hvkc : v k ∈ convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2)) :=
          subset_convexHull ℝ _ (by simp)
        have hconv_h := convex_convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2))
        have h12 : (c0 / (c0 + ci)) • v₀ + (ci / (c0 + ci)) • v i ∈
            convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2)) := by
          apply hconv_h hv0c hvic (div_nonneg hc0.le (by linarith)) (div_nonneg hci.le (by linarith))
          have hpos12 : c0 + ci ≠ 0 := by linarith
          field_simp [hpos12]
        have h123 : (c0 + ci) • ((c0 / (c0 + ci)) • v₀ + (ci / (c0 + ci)) • v i) + ck • v k ∈
            convexHull ℝ ({v₀, v i, v k} : Set (ℝ^2)) :=
          hconv_h h12 hvkc (by linarith) hck.le (by linarith)
        have hsimp : (c0 + ci) • ((c0 / (c0 + ci)) • v₀ + (ci / (c0 + ci)) • v i) + ck • v k = v j := by
          have hpos12 : c0 + ci ≠ 0 := by linarith
          rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos12, mul_div_cancel₀ _ hpos12]
          exact hvec
        rwa [hsimp] at h123
      rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv
      exact hconv (v j) (hv_mem j) hmem_sdiff
    · exact hpos

lemma pz_comb_neg {e1 e2 t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h1 : e1 < 0) (h2 : e2 ≤ 0) :
    (1 - t) * e1 + t * e2 < 0 := by nlinarith

lemma pz_comb_pos {e1 e2 t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h1 : 0 < e1) (h2 : 0 < e2) :
    0 < (1 - t) * e1 + t * e2 := by nlinarith

lemma pz_s_neg {A B s : ℝ} (hs : s ≤ 0) (hA : A < 0) (hB : 0 < B) : (1 - s) * A + s * B < 0 := by
  nlinarith

lemma pz_s_pos {A B s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hA : 0 < A) (hB : 0 < B) :
    0 < (1 - s) * A + s * B := by nlinarith

lemma pz_s_neg' {A B s : ℝ} (hs : 1 < s) (hA : 0 < A) (hB : B < 0) : (1 - s) * A + s * B < 0 := by
  nlinarith

lemma pz_collinear_param {x y z : ℝ^2} (hxy : x ≠ y) (h : orient2 x y z = 0) :
    ∃ s : ℝ, z = (1 - s) • x + s • y := by
  have e : (z 1 - x 1) * (y 0 - x 0) = (z 0 - x 0) * (y 1 - x 1) := by unfold orient2 at h; linarith
  by_cases hx : y 0 - x 0 = 0
  · have hy : y 1 - x 1 ≠ 0 := by
      intro hy; apply hxy; ext i; fin_cases i
      · simp; linarith
      · simp; linarith
    refine ⟨(z 1 - x 1) / (y 1 - x 1), ?_⟩
    have hs : (z 1 - x 1) / (y 1 - x 1) * (y 1 - x 1) = z 1 - x 1 := div_mul_cancel₀ _ hy
    set s := (z 1 - x 1) / (y 1 - x 1)
    have hz0 : z 0 - x 0 = 0 := by
      have : (z 0 - x 0) * (y 1 - x 1) = 0 := by rw [← e, hx, mul_zero]
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hy
    ext i; fin_cases i
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      linarith [show s * (y 0 - x 0) = 0 by rw [hx, mul_zero]]
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      linarith
  · refine ⟨(z 0 - x 0) / (y 0 - x 0), ?_⟩
    have hs : (z 0 - x 0) / (y 0 - x 0) * (y 0 - x 0) = z 0 - x 0 := div_mul_cancel₀ _ hx
    set s := (z 0 - x 0) / (y 0 - x 0)
    have h1 : (s * (y 1 - x 1) - (z 1 - x 1)) * (y 0 - x 0) = 0 := by
      linear_combination (y 1 - x 1) * hs - e
    have h2 : s * (y 1 - x 1) - (z 1 - x 1) = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hx
    ext i; fin_cases i
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      linarith
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      linarith

set_option maxHeartbeats 1000000 in
/-- Positive-fraction Erdős–Szekeres in `ℝ^2` via double-counting convex `2k`-gons. -/
lemma planar_positive_fraction (k : ℕ) (hk : 3 ≤ k) :
    ∃ M : ℕ, 0 < M ∧ ∀ Y : Finset (ℝ^2), DistinctX2 Y → IsGP2 Y → M ≤ Y.card →
      ∃ (Ys : Fin k → Finset (ℝ^2)) (φ : Fin k → (ℝ^2) →ₗ[ℝ] ℝ) (c : Fin k → ℝ),
        (∀ i, Ys i ⊆ Y) ∧
        (∀ i, Y.card ≤ M ^ (2 * k) * (Ys i).card) ∧
        (∀ i, (∀ y ∈ Ys i, φ i y < c i) ∧ (∀ j, j ≠ i → ∀ y ∈ Ys j, c i < φ i y)) ∧
        (∀ a b d : Fin k, a < b → b < d →
          ∀ ya ∈ Ys a, ∀ yb ∈ Ys b, ∀ yd ∈ Ys d, 0 < orient2 ya yb yd) := by
  classical
  let M : ℕ := Nat.choose (4 * k - 4) (2 * k - 2) + 1
  have hMpos : 0 < M := Nat.succ_pos _
  refine ⟨M, hMpos, fun Y hdx hgp hYcard => ?_⟩
  -- Step 1: Double-count convex `2k`-element subsets of `Y`.
  let Conv2k : Finset (Finset (ℝ^2)) := Y.powersetCard (2 * k) |>.filter (fun P : Finset (ℝ^2) =>
    ConvexIndependent ℝ ((↑) : ↥(P : Set (ℝ^2)) → ℝ^2))
  have hcount : Nat.choose Y.card M ≤ Conv2k.card * Nat.choose (Y.card - 2 * k) (M - 2 * k) := by
    let pairs := (Y.powersetCard M).filter (fun _ => True)
    have h2k_le_M : 2 * k ≤ M := by
      have h1 : 2 * k - 2 < 4 * k - 4 := by omega
      have h2 : 4 * k - 4 ≤ Nat.choose (4 * k - 4) (2 * k - 2) := by
        have := Nat.choose_le_choose (2 * k - 2) (le_rfl : 4 * k - 4 ≤ 4 * k - 4)
        -- Use C(2m, m) ≥ 2m for m ≥ 2
        have hm2 : 2 ≤ 2 * k - 2 := by omega
        have hrec : ∀ m : ℕ, 2 ≤ m → 2 * m ≤ Nat.choose (2 * m) m := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => decide
          | succ m hm ihm =>
            have h1' : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
            have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
              rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
              congr 1; omega
            have hstep : Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
              rw [Nat.choose_succ_succ, hsym]; omega
            have hge : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m :=
              Nat.choose_le_choose m (by omega)
            rw [show 2 * (m + 1) = 2 * m + 2 by omega, hstep]
            omega
        have := hrec (2 * k - 2) hm2
        rwa [show 2 * (2 * k - 2) = 4 * k - 4 by omega] at this
      omega
    have hcov : Y.powersetCard M ⊆
        Conv2k.biUnion (fun P => (Y.powersetCard M).filter (fun S => P ⊆ S)) := by
      intro S hS
      have hSY := (Finset.mem_powersetCard.mp hS).1
      have hScard := (Finset.mem_powersetCard.mp hS).2
      have hdxS : DistinctX2 S := fun a ha b hb => hdx a (hSY ha) b (hSY hb)
      have hgpS : IsGP2 S := fun a ha b hb c hc => hgp a (hSY ha) b (hSY hb) c (hSY hc)
      have hScard_gt : Nat.choose (2 * (2 * k) - 4) (2 * k - 2) < S.card := by
        rw [hScard]; simp only [M, show 2 * (2 * k) - 4 = 4 * k - 4 by omega]; omega
      obtain ⟨P, hPS, hPcard, hPconv⟩ := erdos_szekeres_2d (2 * k) (by omega) S hdxS hgpS hScard_gt
      refine Finset.mem_biUnion.mpr ⟨P, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hPS.trans hSY, hPcard⟩, hPconv⟩,
        Finset.mem_filter.mpr ⟨hS, hPS⟩⟩
    have hcard_each : ∀ P ∈ Conv2k,
        ((Y.powersetCard M).filter (fun S => P ⊆ S)).card ≤
          Nat.choose (Y.card - 2 * k) (M - 2 * k) := by
      intro P hP
      have hPY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
      have hPcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
      have hinj : ((Y.powersetCard M).filter (fun S => P ⊆ S)).card ≤
          ((Y \ P).powersetCard (M - 2 * k)).card := by
        refine Finset.card_le_card_of_injOn (fun S => S \ P) (fun S hS => ?_) (fun S₁ hS₁ S₂ hS₂ heq => ?_)
        · have hS' := Finset.mem_filter.mp hS
          have hSY := (Finset.mem_powersetCard.mp hS'.1).1
          have hScard := (Finset.mem_powersetCard.mp hS'.1).2
          refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hSY (Finset.Subset.refl _), ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS'.2, hScard, hPcard]
        · have h1 := (Finset.mem_filter.mp hS₁).2
          have h2 := (Finset.mem_filter.mp hS₂).2
          simp only at heq; rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, heq]
      rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hPY, hPcard] at hinj
      exact hinj
    calc Nat.choose Y.card M = (Y.powersetCard M).card := (Finset.card_powersetCard M Y).symm
      _ ≤ (Conv2k.biUnion (fun P => (Y.powersetCard M).filter (fun S => P ⊆ S))).card :=
          Finset.card_le_card hcov
      _ ≤ ∑ P ∈ Conv2k, ((Y.powersetCard M).filter (fun S => P ⊆ S)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ Conv2k, Nat.choose (Y.card - 2 * k) (M - 2 * k) := Finset.sum_le_sum hcard_each
      _ = Conv2k.card * Nat.choose (Y.card - 2 * k) (M - 2 * k) := by simp
  -- Step 2: From `hcount`, deduce `Y.card ^ (2 * k) ≤ M ^ (2 * k) * Conv2k.card`!
  -- Wait: C(N, M) / C(N - 2k, M - 2k) = C(N, 2k) / C(M, 2k) ≥ (N / M)^(2k)!
  have hconv_lower : Y.card ^ (2 * k) ≤ M ^ (2 * k) * Conv2k.card := by
    have h2k_le_M : 2 * k ≤ M := by
      have hm2 : 2 ≤ 2 * k - 2 := by omega
      have hrec : ∀ m : ℕ, 2 ≤ m → 2 * m ≤ Nat.choose (2 * m) m := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => decide
        | succ m hm ihm =>
          have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
            rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]; congr 1; omega
          have hstep : Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
            rw [Nat.choose_succ_succ, hsym]; omega
          have hge : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m :=
            Nat.choose_le_choose m (by omega)
          rw [show 2 * (m + 1) = 2 * m + 2 by omega, hstep]; omega
      have := hrec (2 * k - 2) hm2
      rw [show 2 * (2 * k - 2) = 4 * k - 4 by omega] at this
      omega
    -- Identity: C(N, M) * C(M, 2k) = C(N, 2k) * C(N - 2k, M - 2k)
    have hid : Nat.choose Y.card M * Nat.choose M (2 * k) =
        Nat.choose Y.card (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k) := by
      have h := Nat.choose_mul (n := Y.card) (k := M) (s := 2 * k) h2k_le_M
      -- Nat.choose_mul : C(n, k) * C(k, s) = C(n, s) * C(n - s, k - s)
      exact h
    -- Also (N / M)^(2k) ≤ C(N, 2k) / C(M, 2k), i.e., N^(2k) * C(M, 2k) ≤ M^(2k) * C(N, 2k)!
    -- Actually even simpler: descFactorial N (2k) / descFactorial M (2k) ≥ (N / M)^(2k) since for 0 ≤ i < 2k,
    -- (N - i) * M ≥ N * (M - i) (because M ≤ N ⇒ i * M ≤ i * N ⇒ N * M - i * N ≤ N * M - i * M)!
    have hdesc : Y.card ^ (2 * k) * M.descFactorial (2 * k) ≤
        M ^ (2 * k) * Y.card.descFactorial (2 * k) := by
      have hgen : ∀ r : ℕ, r ≤ M → Y.card ^ r * M.descFactorial r ≤ M ^ r * Y.card.descFactorial r := by
        intro r hr
        induction r with
        | zero => simp
        | succ r ihr =>
          rw [pow_succ, pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
          have hstep : Y.card * (M - r) ≤ M * (Y.card - r) := by
            have h1 : Y.card * (M - r) + Y.card * r = Y.card * M := by
              rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
            have h2 : M * (Y.card - r) + M * r = M * Y.card := by
              rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
            have h3 : M * r ≤ Y.card * r := Nat.mul_le_mul_right r hYcard
            nlinarith
          have ih' := ihr (by omega)
          calc Y.card ^ r * Y.card * ((M - r) * M.descFactorial r)
              = (Y.card ^ r * M.descFactorial r) * (Y.card * (M - r)) := by ring
            _ ≤ (M ^ r * Y.card.descFactorial r) * (M * (Y.card - r)) :=
                Nat.mul_le_mul ih' hstep
            _ = M ^ r * M * ((Y.card - r) * Y.card.descFactorial r) := by ring
      exact hgen (2 * k) h2k_le_M
    have hch_ineq : Y.card ^ (2 * k) * Nat.choose M (2 * k) ≤
        M ^ (2 * k) * Nat.choose Y.card (2 * k) := by
      have hfac_pos : 0 < (2 * k).factorial := Nat.factorial_pos _
      rw [Nat.choose_eq_descFactorial_div_factorial, Nat.choose_eq_descFactorial_div_factorial]
      have hd1 : (2 * k).factorial ∣ M.descFactorial (2 * k) := Nat.factorial_dvd_descFactorial M (2 * k)
      have hd2 : (2 * k).factorial ∣ Y.card.descFactorial (2 * k) := Nat.factorial_dvd_descFactorial Y.card (2 * k)
      rw [← Nat.mul_div_assoc _ hd1, ← Nat.mul_div_assoc _ hd2]
      exact Nat.div_le_div_right hdesc
    have hpos_ch : 0 < Nat.choose (Y.card - 2 * k) (M - 2 * k) :=
      Nat.choose_pos (by omega)
    have hpos_Mch : 0 < Nat.choose M (2 * k) := Nat.choose_pos h2k_le_M
    have h1 : Y.card ^ (2 * k) * Nat.choose M (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k) ≤
        M ^ (2 * k) * Conv2k.card * Nat.choose M (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k) := by
      calc Y.card ^ (2 * k) * Nat.choose M (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k)
          ≤ M ^ (2 * k) * Nat.choose Y.card (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k) :=
            Nat.mul_le_mul_right _ hch_ineq
        _ = M ^ (2 * k) * (Nat.choose Y.card M * Nat.choose M (2 * k)) := by
            rw [mul_assoc, ← hid]
        _ ≤ M ^ (2 * k) * (Conv2k.card * Nat.choose (Y.card - 2 * k) (M - 2 * k) * Nat.choose M (2 * k)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcount)
        _ = M ^ (2 * k) * Conv2k.card * Nat.choose M (2 * k) * Nat.choose (Y.card - 2 * k) (M - 2 * k) := by
            ring
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right h1 hpos_ch) hpos_Mch
  -- Step 3: For each P ∈ Conv2k, extract a canonical CCW-ordered k-tuple q : Fin k → ℝ^2 (the even vertices).
  have hord : ∀ P ∈ Conv2k, ∃ v : Fin (2 * k) → ℝ^2,
      Function.Injective v ∧ (∀ i, v i ∈ P) ∧
      (∀ i j r : Fin (2 * k), i < j → j < r → 0 < orient2 (v i) (v j) (v r)) := by
    intro P hP
    have hPY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
    have hPcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
    have hPconv := (Finset.mem_filter.mp hP).2
    have hdxP : DistinctX2 P := fun a ha b hb => hdx a (hPY ha) b (hPY hb)
    have hgpP : IsGP2 P := fun a ha b hb c hc => hgp a (hPY ha) b (hPY hb) c (hPY hc)
    obtain ⟨v, hvinj, hvP, hvo⟩ := ccw_order_of_convex_gp (by omega) hdxP hgpP hPconv
    let e : Fin (2 * k) ≃o Fin P.card := Fin.castOrderIso hPcard.symm
    exact ⟨v ∘ e, hvinj.comp e.injective, fun i => hvP (e i), fun i j r hij hjr =>
      hvo (e i) (e j) (e r) (e.strictMono hij) (e.strictMono hjr)⟩
  let vOf (P : Finset (ℝ^2)) : Fin (2 * k) → ℝ^2 :=
    if hP : P ∈ Conv2k then (hord P hP).choose else fun _ => 0
  let qOf (P : Finset (ℝ^2)) : Fin k → ℝ^2 := fun i => vOf P ⟨2 * i.val, by omega⟩
  let pOf (P : Finset (ℝ^2)) : Fin k → ℝ^2 := fun i => vOf P ⟨2 * i.val + 1, by omega⟩
  -- For any CCW k-tuple q : Fin k → ℝ^2, define edge functionals φ_i and regions T_i!
  -- Edge i connects q[i] to q[i+1 mod k]: φ_q i x := orient2 (q i) (q (i+1)) x.
  -- Notice: v[2i] = q[i], v[2i+1] = p[i], v[2i+2] = q[i+1].
  -- For p[i] between q[i] and q[i+1]:
  --   orient2 (q i) (p i) (q (i+1)) > 0  ⇒  orient2 (q i) (q (i+1)) (p i) < 0!
  --   For any other edge j ≠ i: orient2 (q j) (q (j+1)) (p i) > 0!
  let nextIdx (i : Fin k) : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩
  let edgeVal (q : Fin k → ℝ^2) (i : Fin k) (x : ℝ^2) : ℝ := orient2 (q i) (q (nextIdx i)) x
  let regionY (q : Fin k → ℝ^2) (i : Fin k) : Finset (ℝ^2) :=
    Y.filter (fun x => edgeVal q i x < 0 ∧ ∀ j : Fin k, j ≠ i → 0 < edgeVal q j x)
  -- Check that for P ∈ Conv2k, pOf P i ∈ regionY (qOf P) i!
  have hpOf_mem : ∀ P ∈ Conv2k, ∀ i : Fin k, pOf P i ∈ regionY (qOf P) i := by
    intro P hP i
    have hspec := (hord P hP).choose_spec
    have hv_eq : vOf P = (hord P hP).choose := dif_pos hP
    have hPY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
    refine Finset.mem_filter.mpr ⟨hPY (by show vOf P ⟨2 * i.val + 1, by omega⟩ ∈ P; rw [hv_eq]; exact hspec.2.1 _), ?_, ?_⟩
    · -- edgeVal (qOf P) i (pOf P i) < 0
      dsimp only [edgeVal, qOf, pOf, nextIdx]
      rw [hv_eq]
      by_cases hi : i.val + 1 < k
      · have hmod : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt hi
        have h1 := hspec.2.2 ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩
          ⟨2 * (i.val + 1), by omega⟩ (by simp [Fin.lt_def]) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
        have hswap := orient2_swap23 ((hord P hP).choose ⟨2 * i.val, by omega⟩)
          ((hord P hP).choose ⟨2 * i.val + 1, by omega⟩)
          ((hord P hP).choose ⟨2 * (i.val + 1), by omega⟩)
        simp only [hmod]
        linarith
      · have hi_eq : i.val = k - 1 := by omega
        have hmod : (i.val + 1) % k = 0 := by rw [hi_eq, show k - 1 + 1 = k by omega, Nat.mod_self]
        have h1 := hspec.2.2 ⟨0, by omega⟩ ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩
          (by simp only [Fin.lt_def, Fin.val_mk]; omega) (by simp [Fin.lt_def])
        have hcyc := orient2_cycle ((hord P hP).choose ⟨0, by omega⟩)
          ((hord P hP).choose ⟨2 * i.val, by omega⟩)
          ((hord P hP).choose ⟨2 * i.val + 1, by omega⟩)
        have hswap := orient2_swap23 ((hord P hP).choose ⟨2 * i.val, by omega⟩)
          ((hord P hP).choose ⟨2 * i.val + 1, by omega⟩)
          ((hord P hP).choose ⟨0, by omega⟩)
        simp only [hmod, mul_zero]
        linarith
    · -- For j ≠ i, 0 < edgeVal (qOf P) j (pOf P i)
      intro j hji
      dsimp only [edgeVal, qOf, pOf, nextIdx]
      rw [hv_eq]
      by_cases hj : j.val + 1 < k
      · have hmod : (j.val + 1) % k = j.val + 1 := Nat.mod_eq_of_lt hj
        simp only [hmod]
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hji) with hlt | hgt
        · exact hspec.2.2 ⟨2 * j.val, by omega⟩ ⟨2 * (j.val + 1), by omega⟩
            ⟨2 * i.val + 1, by omega⟩ (by simp only [Fin.lt_def, Fin.val_mk]; omega) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
        · have h1 := hspec.2.2 ⟨2 * i.val + 1, by omega⟩ ⟨2 * j.val, by omega⟩
            ⟨2 * (j.val + 1), by omega⟩ (by simp only [Fin.lt_def, Fin.val_mk]; omega) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
          rw [orient2_cycle] at h1
          exact h1
      · have hj_eq : j.val = k - 1 := by omega
        have hmod : (j.val + 1) % k = 0 := by rw [hj_eq, show k - 1 + 1 = k by omega, Nat.mod_self]
        simp only [hmod, mul_zero]
        have hi_lt : i.val < k - 1 := by
          have := i.isLt; have := Fin.val_ne_of_ne hji; omega
        have h1 := hspec.2.2 ⟨0, by omega⟩ ⟨2 * i.val + 1, by omega⟩ ⟨2 * j.val, by omega⟩
          (by simp [Fin.lt_def]) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
        rw [orient2_cycle, orient2_cycle] at h1
        exact h1
  -- Step 4: Pigeonhole over `q` ∈ `Conv2k.image qOf`!
  -- Every `q` in `Conv2k.image qOf` has `q i ∈ Y`, so `(Conv2k.image qOf).card ≤ Y.card ^ k`!
  let Qset := Conv2k.image qOf
  have hQcard : Qset.card ≤ Y.card ^ k := by
    have hsub : Qset ⊆ Fintype.piFinset (fun _ : Fin k => Y) := by
      intro q hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      rw [Fintype.mem_piFinset]
      intro i
      have hPY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
      have hspec := (hord P hP).choose_spec
      dsimp only [qOf, vOf]
      rw [dif_pos hP]
      exact hPY (hspec.2.1 _)
    calc Qset.card ≤ (Fintype.piFinset (fun _ : Fin k => Y)).card := Finset.card_le_card hsub
      _ = Y.card ^ k := by rw [Fintype.card_piFinset]; simp
  have hConv_pos : 0 < Conv2k.card := by
    have hYpos : 0 < Y.card ^ (2 * k) := pow_pos (by omega) _
    by_contra h0; simp only [not_lt, Nat.le_zero] at h0
    rw [h0, mul_zero] at hconv_lower; omega
  have hQne : Qset.Nonempty := Finset.Nonempty.image (Finset.card_pos.mp hConv_pos) qOf
  -- Fiber size bound: for each `q ∈ Qset`, the fiber `Conv2k.filter (qOf · = q)` injects into
  -- `Fintype.piFinset (regionY q)` via `pOf`!
  have hfiber : ∀ q ∈ Qset,
      (Conv2k.filter (fun P => qOf P = q)).card ≤ ∏ i : Fin k, (regionY q i).card := by
    intro q hq
    rw [← Fintype.card_piFinset]
    refine Finset.card_le_card_of_injOn pOf (fun P hP => ?_) (fun P₁ hP₁ P₂ hP₂ heq => ?_)
    · have hP' := Finset.mem_filter.mp hP
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      rw [← hP'.2]
      exact hpOf_mem P hP'.1 i
    · have h1 := Finset.mem_filter.mp hP₁
      have h2 := Finset.mem_filter.mp hP₂
      -- P₁ and P₂ have the same `qOf` and same `pOf`, hence the same `vOf`, hence P₁ = P₂!
      have hv_eq : vOf P₁ = vOf P₂ := by
        funext idx
        have hidxlt := idx.isLt
        rcases Nat.even_or_odd idx.val with ⟨m, hm⟩ | ⟨m, hm⟩
        · have hm_lt : m < k := by omega
          have h12 := congrFun (h1.2.trans h2.2.symm) ⟨m, hm_lt⟩
          have hidx : idx = ⟨2 * m, by omega⟩ := Fin.ext (by show idx.val = 2 * m; omega)
          rw [hidx]; exact h12
        · have hm_lt : m < k := by omega
          have h12 := congrFun heq ⟨m, hm_lt⟩
          have hidx : idx = ⟨2 * m + 1, by omega⟩ := Fin.ext (by show idx.val = 2 * m + 1; omega)
          rw [hidx]; exact h12
      -- Every P ∈ Conv2k equals `Finset.univ.image (vOf P)`!
      have him_eq : ∀ P ∈ Conv2k, Finset.univ.image (vOf P) = P := fun P hP => by
        have hspec := (hord P hP).choose_spec
        have hcardP := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          dsimp only [vOf]; rw [dif_pos hP]; exact hspec.2.1 i
        · rw [Finset.card_image_of_injective _ (by dsimp only [vOf]; rw [dif_pos hP]; exact hspec.1),
              Finset.card_fin, hcardP]
      rw [← him_eq P₁ h1.1, ← him_eq P₂ h2.1, hv_eq]
  -- Pick `q ∈ Qset` maximizing fiber size!
  obtain ⟨q, hqQ, hqmax⟩ := Finset.exists_max_image Qset (fun q => (Conv2k.filter (fun P => qOf P = q)).card) hQne
  have hsum_fibers : Conv2k.card = ∑ q' ∈ Qset, (Conv2k.filter (fun P => qOf P = q')).card := by
    rw [Finset.card_eq_sum_card_image qOf Conv2k]
  have hprod_ge : Y.card ^ k ≤ M ^ (2 * k) * ∏ i : Fin k, (regionY q i).card := by
    have h1 : Conv2k.card ≤ Qset.card * (Conv2k.filter (fun P => qOf P = q)).card := by
      rw [hsum_fibers]
      calc ∑ q' ∈ Qset, (Conv2k.filter (fun P => qOf P = q')).card
          ≤ ∑ _q' ∈ Qset, (Conv2k.filter (fun P => qOf P = q)).card :=
            Finset.sum_le_sum fun q' hq' => hqmax q' hq'
        _ = Qset.card * (Conv2k.filter (fun P => qOf P = q)).card := by simp
    have h2 : Y.card ^ (2 * k) ≤ M ^ (2 * k) * (Y.card ^ k * ∏ i : Fin k, (regionY q i).card) := by
      calc Y.card ^ (2 * k) ≤ M ^ (2 * k) * Conv2k.card := hconv_lower
        _ ≤ M ^ (2 * k) * (Qset.card * (Conv2k.filter (fun P => qOf P = q)).card) :=
            Nat.mul_le_mul_left _ h1
        _ ≤ M ^ (2 * k) * (Y.card ^ k * ∏ i : Fin k, (regionY q i).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hQcard (hfiber q hqQ))
    have hpow : Y.card ^ (2 * k) = Y.card ^ k * Y.card ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [hpow] at h2
    have hYk_pos : 0 < Y.card ^ k := pow_pos (by omega) _
    have h3 : Y.card ^ k * Y.card ^ k ≤ Y.card ^ k * (M ^ (2 * k) * ∏ i : Fin k, (regionY q i).card) := by
      linarith
    exact Nat.le_of_mul_le_mul_left h3 hYk_pos
  -- Each factor `(regionY q i).card` satisfies `Y.card ≤ M ^ (2 * k) * (regionY q i).card`!
  have hfactor : ∀ i : Fin k, Y.card ≤ M ^ (2 * k) * (regionY q i).card := by
    intro i
    have hrest_le : ∏ j ∈ Finset.univ.erase i, (regionY q j).card ≤ Y.card ^ (k - 1) := by
      calc ∏ j ∈ Finset.univ.erase i, (regionY q j).card
          ≤ ∏ _j ∈ Finset.univ.erase i, Y.card :=
            Finset.prod_le_prod' fun j _ => Finset.card_le_card (Finset.filter_subset _ _)
        _ = Y.card ^ (k - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    have hsplit : ∏ j : Fin k, (regionY q j).card =
        (regionY q i).card * ∏ j ∈ Finset.univ.erase i, (regionY q j).card :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
    have hpow : Y.card ^ k = Y.card * Y.card ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) by omega, pow_add, pow_one]
    have h1 : Y.card * Y.card ^ (k - 1) ≤ M ^ (2 * k) * (regionY q i).card * Y.card ^ (k - 1) := by
      calc Y.card * Y.card ^ (k - 1) = Y.card ^ k := hpow.symm
        _ ≤ M ^ (2 * k) * ∏ j : Fin k, (regionY q j).card := hprod_ge
        _ = M ^ (2 * k) * ((regionY q i).card * ∏ j ∈ Finset.univ.erase i, (regionY q j).card) := by
            rw [hsplit]
        _ ≤ M ^ (2 * k) * ((regionY q i).card * Y.card ^ (k - 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrest_le)
        _ = M ^ (2 * k) * (regionY q i).card * Y.card ^ (k - 1) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos (by omega) _)
  -- Extract CCW property of `q` from `q ∈ Qset`:
  obtain ⟨P₀, hP₀, hq_eq⟩ := Finset.mem_image.mp hqQ
  have hq_ccw : ∀ a b d : Fin k, a < b → b < d → 0 < orient2 (q a) (q b) (q d) := by
    intro a b d hab hbd
    rw [← hq_eq]
    have hspec := (hord P₀ hP₀).choose_spec
    dsimp only [qOf, vOf]; rw [dif_pos hP₀]
    exact hspec.2.2 ⟨2 * a.val, by omega⟩ ⟨2 * b.val, by omega⟩ ⟨2 * d.val, by omega⟩
      (by simp only [Fin.lt_def, Fin.val_mk]; omega) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
  -- Linear functional for edge i: orient2 (q i) (q (nextIdx i)) x = φ i x - c i!
  let φ : Fin k → (ℝ^2) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun x =>
        (q (nextIdx i) 0 - q i 0) * x 1 - (q (nextIdx i) 1 - q i 1) * x 0
      map_add' := fun x y => by simp; ring
      map_smul' := fun r x => by simp; ring }
  let c : Fin k → ℝ := fun i =>
    (q (nextIdx i) 0 - q i 0) * q i 1 - (q (nextIdx i) 1 - q i 1) * q i 0
  have hedge_eq : ∀ i x, edgeVal q i x = φ i x - c i := fun i x => by
    simp only [edgeVal, orient2, φ, c, LinearMap.coe_mk, AddHom.coe_mk]; ring
  -- Step 5: Prove CCW orientation for ANY ya ∈ regionY q a, yb ∈ regionY q b, yd ∈ regionY q d (a < b < d)!
  have hccw_regions : ∀ a b d : Fin k, a < b → b < d →
      ∀ ya ∈ regionY q a, ∀ yb ∈ regionY q b, ∀ yd ∈ regionY q d, 0 < orient2 ya yb yd := by
    intro a b d hab hbd ya hya yb hyb yd hyd
    have hya' := (Finset.mem_filter.mp hya).2
    have hyb' := (Finset.mem_filter.mp hyb).2
    have hyd' := (Finset.mem_filter.mp hyd).2
    -- Midpoints m_i = (1/2) • (q i + q (nextIdx i))
    let m (i : Fin k) : ℝ^2 := (1 / 2 : ℝ) • (q i + q (nextIdx i))
    -- edgeVal q i (m i) = 0 and edgeVal q j (m i) > 0 for j ≠ i!
    have hm_edge_nonneg : ∀ j i : Fin k, 0 ≤ edgeVal q j (q i) := fun j i => by
      dsimp only [edgeVal, nextIdx]
      by_cases h1 : i = j
      · subst h1; rw [orient2_self_outer]
      · by_cases h2 : i = ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        · rw [h2, orient2_self_right]
        · by_cases hj : j.val + 1 < k
          · have hmod : (j.val + 1) % k = j.val + 1 := Nat.mod_eq_of_lt hj
            have hi_ne1 : i.val ≠ j.val := Fin.val_ne_of_ne h1
            have hi_ne2 : i.val ≠ j.val + 1 := fun h => h2 (Fin.ext (by simp [hmod, h]))
            rcases lt_or_gt_of_ne hi_ne1 with hlt | hgt
            · have hpos := hq_ccw i j ⟨j.val + 1, hj⟩ hlt (by simp [Fin.lt_def])
              rw [orient2_cycle] at hpos
              simpa [hmod] using hpos.le
            · have hpos := hq_ccw j ⟨j.val + 1, hj⟩ i (by simp [Fin.lt_def]) (by simp only [Fin.lt_def, Fin.val_mk]; omega)
              simpa [hmod] using hpos.le
          · have hj_eq : j.val = k - 1 := by omega
            have hmod : (j.val + 1) % k = 0 := by rw [hj_eq, show k - 1 + 1 = k by omega, Nat.mod_self]
            have hi_ne0 : i.val ≠ 0 := fun h => h2 (Fin.ext (by simp [hmod, h]))
            have hi_lt : i.val < j.val := by
              have := i.isLt; have := Fin.val_ne_of_ne h1; omega
            have hpos := hq_ccw ⟨0, by omega⟩ i j (by simp only [Fin.lt_def, Fin.val_mk]; omega) hi_lt
            rw [orient2_cycle, orient2_cycle] at hpos
            simpa [hmod] using hpos.le
    have hm_edge_pos : ∀ j i : Fin k, j ≠ i → 0 < edgeVal q j (m i) := fun j i hji => by
      have hlin : edgeVal q j (m i) = (edgeVal q j (q i) + edgeVal q j (q (nextIdx i))) / 2 := by
        simp only [edgeVal, m, orient2, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; ring
      rw [hlin]
      have hnn1 := hm_edge_nonneg j i
      have hnn2 := hm_edge_nonneg j (nextIdx i)
      -- At least one of q i, q (nextIdx i) is NOT equal to q j or q (nextIdx j)!
      have hnotboth : ¬ ((i = j ∨ i = nextIdx j) ∧ (nextIdx i = j ∨ nextIdx i = nextIdx j)) := by
        rintro ⟨h1 | h1, h2 | h2⟩
        · exact hji h1.symm
        · exact hji h1.symm
        · -- i = nextIdx j and nextIdx i = j ⇒ (j + 2) % k = j, impossible since k ≥ 3!
          have hv1 : i.val = (j.val + 1) % k := congrArg Fin.val h1
          have hv2 : (i.val + 1) % k = j.val := congrArg Fin.val h2
          have := j.isLt; have := i.isLt
          have hmod2 : (j.val + 2) % k = j.val := by
            rw [show j.val + 2 = (j.val + 1) + 1 by omega, ← Nat.mod_add_mod, ← hv1]; exact hv2
          by_cases hcase : j.val + 2 < k
          · rw [Nat.mod_eq_of_lt hcase] at hmod2; omega
          · have : j.val + 2 - k < k := by omega
            have hsub : (j.val + 2) % k = j.val + 2 - k := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
            rw [hsub] at hmod2; omega
        · -- nextIdx i = nextIdx j ⇒ i = j!
          have hv : (i.val + 1) % k = (j.val + 1) % k := congrArg Fin.val h2
          apply hji; apply Fin.ext
          have := i.isLt; have := j.isLt
          by_cases hi1 : i.val + 1 < k <;> by_cases hj1 : j.val + 1 < k
          · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at hv; omega
          · rw [Nat.mod_eq_of_lt hi1, show j.val + 1 = k by omega, Nat.mod_self] at hv; omega
          · rw [Nat.mod_eq_of_lt hj1, show i.val + 1 = k by omega, Nat.mod_self] at hv; omega
          · omega
      have hstrict : ∀ r : Fin k, r ≠ j → r ≠ nextIdx j → 0 < edgeVal q j (q r) := fun r h1 h2 => by
        have hnn := hm_edge_nonneg j r
        have hne0 : edgeVal q j (q r) ≠ 0 := by
          dsimp only [edgeVal]
          have hq_inj : Function.Injective q := by
            intro x y hxy
            by_contra hne
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
            · -- Pick a third index distinct from x, y
              have hP₀' := (hord P₀ hP₀).choose_spec.1
              rw [← hq_eq] at hxy
              dsimp only [qOf, vOf] at hxy
              rw [dif_pos hP₀] at hxy
              have := congrArg Fin.val (hP₀' hxy)
              (try simp only [Fin.val_mk] at this); omega
            · have hP₀' := (hord P₀ hP₀).choose_spec.1
              rw [← hq_eq] at hxy
              dsimp only [qOf, vOf] at hxy
              rw [dif_pos hP₀] at hxy
              have := congrArg Fin.val (hP₀' hxy)
              (try simp only [Fin.val_mk] at this); omega
          have hj_ne_nj : j ≠ nextIdx j := fun heq => by
            have hv := congrArg Fin.val heq
            dsimp only [nextIdx] at hv
            have := j.isLt
            by_cases hlt : j.val + 1 < k
            · rw [Nat.mod_eq_of_lt hlt] at hv; omega
            · rw [show j.val + 1 = k by omega, Nat.mod_self] at hv; omega
          have hqY : ∀ x, q x ∈ Y := fun x => by
            rw [← hq_eq]; dsimp only [qOf, vOf]; rw [dif_pos hP₀]
            exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP₀).1).1
              ((hord P₀ hP₀).choose_spec.2.1 _)
          exact hgp (q j) (hqY j) (q (nextIdx j)) (hqY _) (q r) (hqY r)
            (fun h => hj_ne_nj (hq_inj h))
            (fun h => h2 (hq_inj h).symm)
            (fun h => h1 (hq_inj h).symm)
        exact lt_of_le_of_ne hnn hne0.symm
      by_cases h1 : i = j ∨ i = nextIdx j
      · have h2 : nextIdx i ≠ j ∧ nextIdx i ≠ nextIdx j := by tauto
        have hpos := hstrict (nextIdx i) h2.1 h2.2
        linarith
      · push_neg at h1
        have hpos := hstrict i h1.1 h1.2
        linarith
    have hm_edge_zero : ∀ i : Fin k, edgeVal q i (m i) = 0 := fun i => by
      simp only [edgeVal, m, orient2, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; ring
    -- Check orient2 (m a) (m b) (m d) > 0 by multilinearity!
    have hm_pos : 0 < orient2 (m a) (m b) (m d) := by
      have hexpand : orient2 (m a) (m b) (m d) =
          (orient2 (q a) (q b) (q d) + orient2 (q a) (q b) (q (nextIdx d)) +
           orient2 (q a) (q (nextIdx b)) (q d) + orient2 (q a) (q (nextIdx b)) (q (nextIdx d)) +
           orient2 (q (nextIdx a)) (q b) (q d) + orient2 (q (nextIdx a)) (q b) (q (nextIdx d)) +
           orient2 (q (nextIdx a)) (q (nextIdx b)) (q d) +
           orient2 (q (nextIdx a)) (q (nextIdx b)) (q (nextIdx d))) / 8 := by
        simp only [m, orient2, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; ring
      rw [hexpand]
      have hterm1 : 0 < orient2 (q a) (q b) (q d) := hq_ccw a b d hab hbd
      have hccw_nn : ∀ u v w : Fin k,
          (u ≤ v ∧ v ≤ w) ∨ (v ≤ w ∧ w ≤ u) ∨ (w ≤ u ∧ u ≤ v) →
          0 ≤ orient2 (q u) (q v) (q w) := by
        intro u v w hord3
        rcases hord3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · by_cases he1 : u = v; · subst he1; rw [orient2_self_left]
          by_cases he2 : v = w; · subst he2; rw [orient2_self_right]
          exact (hq_ccw u v w (lt_of_le_of_ne h1 he1) (lt_of_le_of_ne h2 he2)).le
        · rw [orient2_cycle]
          by_cases he1 : v = w; · subst he1; rw [orient2_self_left]
          by_cases he2 : w = u; · subst he2; rw [orient2_self_right]
          exact (hq_ccw v w u (lt_of_le_of_ne h1 he1) (lt_of_le_of_ne h2 he2)).le
        · rw [orient2_cycle, orient2_cycle]
          by_cases he1 : w = u; · subst he1; rw [orient2_self_left]
          by_cases he2 : u = v; · subst he2; rw [orient2_self_right]
          exact (hq_ccw w u v (lt_of_le_of_ne h1 he1) (lt_of_le_of_ne h2 he2)).le
      have hna : a.val + 1 ≤ b.val := by have := Fin.lt_def.mp hab; omega
      have hnb : b.val + 1 ≤ d.val := by have := Fin.lt_def.mp hbd; omega
      have hna_eq : (nextIdx a).val = a.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hnb_eq : (nextIdx b).val = b.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hnd_cases : (nextIdx d).val = d.val + 1 ∨ (nextIdx d).val = 0 := by
        dsimp only [nextIdx]
        by_cases hd : d.val + 1 < k
        · left; exact Nat.mod_eq_of_lt hd
        · right; rw [show d.val + 1 = k by omega, Nat.mod_self]
      have hle : ∀ x y : Fin k, x.val ≤ y.val → x ≤ y := fun x y h => Fin.le_iff_val_le_val.mpr h
      have hnn : ∀ u v w : Fin k, (u = a ∨ u = nextIdx a) → (v = b ∨ v = nextIdx b) →
          (w = d ∨ w = nextIdx d) → 0 ≤ orient2 (q u) (q v) (q w) := by
        intro u v w hu hv hw
        apply hccw_nn
        rcases hnd_cases with hnd1 | hnd0
        · left
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
            exact ⟨hle _ _ (by omega), hle _ _ (by omega)⟩
        · rcases hw with rfl | rfl
          · left
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
              exact ⟨hle _ _ (by omega), hle _ _ (by omega)⟩
          · right; right
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
              exact ⟨hle _ _ (by omega), hle _ _ (by omega)⟩
      have h2 := hnn a b (nextIdx d) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
      have h3 := hnn a (nextIdx b) d (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
      have h4 := hnn a (nextIdx b) (nextIdx d) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
      have h5 := hnn (nextIdx a) b d (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
      have h6 := hnn (nextIdx a) b (nextIdx d) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
      have h7 := hnn (nextIdx a) (nextIdx b) d (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
      have h8 := hnn (nextIdx a) (nextIdx b) (nextIdx d) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      linarith
    -- Define straight-line homotopy z_i(t) = (1-t) • y_i + t • m_i on [0, 1]!
    let za (t : ℝ) : ℝ^2 := (1 - t) • ya + t • m a
    let zb (t : ℝ) : ℝ^2 := (1 - t) • yb + t • m b
    let zd (t : ℝ) : ℝ^2 := (1 - t) • yd + t • m d
    let F (t : ℝ) : ℝ := orient2 (za t) (zb t) (zd t)
    have hF_cont : Continuous F := by
      unfold F orient2 za zb zd
      fun_prop
    have hF1 : 0 < F 1 := by
      simp only [F, za, zb, zd, sub_self, zero_smul, zero_add, one_smul]; exact hm_pos
    have hF_ne0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≠ 0 := by
      intro t ht hFt0
      by_cases ht1 : t = 1
      · subst ht1; linarith
      · have ht0 : 0 ≤ t := ht.1
        have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
        have h1mt : 0 < 1 - t := sub_pos.mpr htlt
        have hedge_lin : ∀ i x y, edgeVal q i ((1 - t) • x + t • y) =
            (1 - t) * edgeVal q i x + t * edgeVal q i y := fun i x y => by
          rw [hedge_eq, hedge_eq, hedge_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          ring
        have hab_ne : a ≠ b := ne_of_lt hab
        have hbd_ne : b ≠ d := ne_of_lt hbd
        have had_ne : a ≠ d := ne_of_lt (hab.trans hbd)
        have hza_a : edgeVal q a (za t) < 0 := by
          rw [hedge_lin, hm_edge_zero]; exact pz_comb_neg ht0 htlt hya'.1 le_rfl
        have hza_b : 0 < edgeVal q b (za t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hya'.2 b hab_ne.symm) (hm_edge_pos b a hab_ne.symm)
        have hza_d : 0 < edgeVal q d (za t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hya'.2 d had_ne.symm) (hm_edge_pos d a had_ne.symm)
        have hzb_a : 0 < edgeVal q a (zb t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hyb'.2 a hab_ne) (hm_edge_pos a b hab_ne)
        have hzb_b : edgeVal q b (zb t) < 0 := by
          rw [hedge_lin, hm_edge_zero]; exact pz_comb_neg ht0 htlt hyb'.1 le_rfl
        have hzb_d : 0 < edgeVal q d (zb t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hyb'.2 d hbd_ne.symm) (hm_edge_pos d b hbd_ne.symm)
        have hzd_a : 0 < edgeVal q a (zd t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hyd'.2 a had_ne) (hm_edge_pos a d had_ne)
        have hzd_b : 0 < edgeVal q b (zd t) := by
          rw [hedge_lin]; exact pz_comb_pos ht0 htlt (hyd'.2 b hbd_ne) (hm_edge_pos b d hbd_ne)
        have hzd_d : edgeVal q d (zd t) < 0 := by
          rw [hedge_lin, hm_edge_zero]; exact pz_comb_neg ht0 htlt hyd'.1 le_rfl
        -- Since orient2 (za t) (zb t) (zd t) = 0, one of za t, zb t, zd t is a convex combination of the other two!
        have hzab_ne : za t ≠ zb t := fun h => by rw [h] at hza_a; linarith
        -- Write zd t = (1 - s) • za t + s • zb t for some s : ℝ!
        have hex_s : ∃ s : ℝ, zd t = (1 - s) • za t + s • zb t := pz_collinear_param hzab_ne hFt0
        obtain ⟨s, hs⟩ := hex_s
        have hlin_s : ∀ i, edgeVal q i (zd t) = (1 - s) * edgeVal q i (za t) + s * edgeVal q i (zb t) :=
          fun i => by rw [hs, hedge_eq, hedge_eq, hedge_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
        rcases le_or_gt s 0 with hs0 | hs0
        · -- s ≤ 0 ⇒ za t is between zd t and zb t: (1 - s) > 0, so edgeVal a (zd t) = (1-s) edgeVal a (za t) + s edgeVal a (zb t) < 0, contradiction!
          have := hlin_s a; have := pz_s_neg hs0 hza_a hzb_a; linarith
        · rcases le_or_gt s 1 with hs1 | hs1
          · -- 0 < s ≤ 1 ⇒ zd t is between za t and zb t: edgeVal d (zd t) = (1-s) edgeVal d (za t) + s edgeVal d (zb t) > 0, contradiction!
            have := hlin_s d; have := pz_s_pos hs0 hs1 hza_d hzb_d; linarith
          · -- s > 1 ⇒ zb t is between za t and zd t: edgeVal b (zd t) = (1-s) edgeVal b (za t) + s edgeVal b (zb t) < 0, contradiction!
            have := hlin_s b; have := pz_s_neg' hs1 hza_b hzb_b; linarith
    -- By IVT on [0, 1], since F 1 > 0 and F t ≠ 0 on [0, 1], F 0 > 0!
    by_contra hle0
    push_neg at hle0
    have hF0_le : F 0 ≤ 0 := by
      simpa only [F, za, zb, zd, sub_zero, one_smul, zero_smul, add_zero] using hle0
    have h0mem : (0 : ℝ) ∈ Set.Icc (F 0) (F 1) := ⟨hF0_le, hF1.le⟩
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hF_cont.continuousOn h0mem
    exact hF_ne0 t ht hFt
  refine ⟨regionY q, φ, c, fun i => Finset.filter_subset _ _, hfactor, ?_, hccw_regions⟩
  intro i
  constructor
  · intro y hy
    have hlt := (Finset.mem_filter.mp hy).2.1
    rw [hedge_eq] at hlt; linarith
  · intro j hji y hy
    have hgt := (Finset.mem_filter.mp hy).2.2 i hji.symm
    rw [hedge_eq] at hgt; linarith

/-! ## Section 5: 3D Orthant Cups-vs-Caps (Proposition 2.3) -/

def PosOctant : Set (ℝ^3) := {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2}
def PosQuad : Set (ℝ^2) := {p | 0 ≤ p 0 ∧ 0 ≤ p 1}

def IsCFree (C : Set (ℝ^3)) (X : Finset (ℝ^3)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ t : ℝ, (1 - t) • x + t • y ∉ C

def IsCCap (C : Set (ℝ^3)) (K : Finset (ℝ^3)) : Prop :=
  ∀ x ∈ K, x ∉ convexHull ℝ (C ∪ ((K.erase x : Finset (ℝ^3)) : Set (ℝ^3)))

/-- Drop coordinate `i` from `ℝ^3` to `ℝ^2`. -/
def proj3 (i : Fin 3) : (ℝ^3) →ₗ[ℝ] (ℝ^2) :=
  match i with
  | ⟨0, _⟩ => { toFun := fun u => !₂[u 1, u 2], map_add' := fun u v => by ext k; fin_cases k <;> simp,
                map_smul' := fun r u => by ext k; fin_cases k <;> simp }
  | ⟨1, _⟩ => { toFun := fun u => !₂[u 0, u 2], map_add' := fun u v => by ext k; fin_cases k <;> simp,
                map_smul' := fun r u => by ext k; fin_cases k <;> simp }
  | ⟨2, _⟩ => { toFun := fun u => !₂[u 0, u 1], map_add' := fun u v => by ext k; fin_cases k <;> simp,
                map_smul' := fun r u => by ext k; fin_cases k <;> simp }

lemma proj3_posOctant (i : Fin 3) {u : ℝ^3} (hu : u ∈ PosOctant) : proj3 i u ∈ PosQuad := by
  obtain ⟨h0, h1, h2⟩ := hu
  fin_cases i <;> simp [proj3, PosQuad] <;> tauto

/-- 1D Helly for 3 linear rays: if no `t` satisfies all three `a_k + t * d_k ≥ 0`, then some pair is disjoint. -/
lemma helly_1d_three (a₀ d₀ a₁ d₁ a₂ d₂ : ℝ)
    (h : ∀ t : ℝ, ¬ (0 ≤ a₀ + t * d₀ ∧ 0 ≤ a₁ + t * d₁ ∧ 0 ≤ a₂ + t * d₂)) :
    (∀ t : ℝ, ¬ (0 ≤ a₁ + t * d₁ ∧ 0 ≤ a₂ + t * d₂)) ∨
    (∀ t : ℝ, ¬ (0 ≤ a₀ + t * d₀ ∧ 0 ≤ a₂ + t * d₂)) ∨
    (∀ t : ℝ, ¬ (0 ≤ a₀ + t * d₀ ∧ 0 ≤ a₁ + t * d₁)) := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨⟨t₀, ht₀1, ht₀2⟩, ⟨t₁, ht₁0, ht₁2⟩, ⟨t₂, ht₂0, ht₂1⟩⟩ := hnot
  -- The middle value among {t₀, t₁, t₂} lies in all three convex intervals!
  have hmid : ∀ x y z : ℝ, x ≤ y → y ≤ z →
      (∀ a d : ℝ, 0 ≤ a + x * d → 0 ≤ a + z * d → 0 ≤ a + y * d) := by
    intro x y z hxy hyz a d hx hz
    by_cases hxz : x = z
    · have : y = x := le_antisymm (hxz ▸ hyz) hxy
      rwa [this]
    · have hpos : 0 < z - x := sub_pos.mpr (lt_of_le_of_ne (hxy.trans hyz) hxz)
      have hlin : a + y * d = ((z - y) * (a + x * d) + (y - x) * (a + z * d)) / (z - x) := by
        field_simp [hpos.ne']; ring
      rw [hlin]
      exact div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hyz) hx)
        (mul_nonneg (sub_nonneg.mpr hxy) hz)) hpos.le
  rcases le_total t₀ t₁ with h01 | h10
  · rcases le_total t₁ t₂ with h12 | h21
    · -- t₀ ≤ t₁ ≤ t₂
      exact h t₁ ⟨ht₁0, hmid t₀ t₁ t₂ h01 h12 a₁ d₁ ht₀1 ht₂1, ht₁2⟩
    · rcases le_total t₀ t₂ with h02 | h20
      · -- t₀ ≤ t₂ ≤ t₁
        exact h t₂ ⟨ht₂0, ht₂1, hmid t₀ t₂ t₁ h02 h21 a₂ d₂ ht₀2 ht₁2⟩
      · -- t₂ ≤ t₀ ≤ t₁
        exact h t₀ ⟨hmid t₂ t₀ t₁ h20 h01 a₀ d₀ ht₂0 ht₁0, ht₀1, ht₀2⟩
  · rcases le_total t₀ t₂ with h02 | h20
    · -- t₁ ≤ t₀ ≤ t₂
      exact h t₀ ⟨hmid t₁ t₀ t₂ h10 h02 a₀ d₀ ht₁0 ht₂0, ht₀1, ht₀2⟩
    · rcases le_total t₁ t₂ with h12 | h21
      · -- t₁ ≤ t₂ ≤ t₀
        exact h t₂ ⟨ht₂0, ht₂1, hmid t₁ t₂ t₀ h12 h20 a₂ d₂ ht₁2 ht₀2⟩
      · -- t₂ ≤ t₁ ≤ t₀
        exact h t₁ ⟨ht₁0, hmid t₂ t₁ t₀ h21 h10 a₁ d₁ ht₂1 ht₀1, ht₁2⟩

lemma mem_convexHull_posQuad_insert {p q : ℝ^2} :
    p ∈ convexHull ℝ (PosQuad ∪ {q}) ↔
      ∃ (t : ℝ) (r : ℝ^2), 0 ≤ t ∧ t ≤ 1 ∧ r ∈ PosQuad ∧ p = (1 - t) • q + t • r := by
  have hQconv : Convex ℝ PosQuad := by
    intro x hx y hy a b ha hb _
    simp only [PosQuad, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    exact ⟨by nlinarith, by nlinarith⟩
  have hQne : PosQuad.Nonempty := ⟨0, by simp [PosQuad]⟩
  constructor
  · intro hp
    have hsub : convexHull ℝ (PosQuad ∪ {q}) ⊆
        {x | ∃ (t : ℝ) (r : ℝ^2), 0 ≤ t ∧ t ≤ 1 ∧ r ∈ PosQuad ∧ x = (1 - t) • q + t • r} := by
      apply convexHull_min
      · rintro x (hxQ | rfl)
        · exact ⟨1, x, zero_le_one, le_rfl, hxQ, by simp⟩
        · exact ⟨0, 0, le_rfl, zero_le_one, by simp [PosQuad], by simp⟩
      · rintro x ⟨t₁, r₁, ht₁0, ht₁1, hr₁, rfl⟩ y ⟨t₂, r₂, ht₂0, ht₂1, hr₂, rfl⟩ a b ha hb hab
        let t := a * t₁ + b * t₂
        have ht0 : 0 ≤ t := by nlinarith
        have ht1 : t ≤ 1 := by nlinarith
        by_cases htz : t = 0
        · have hsum0 : a * t₁ + b * t₂ = 0 := htz
          have hn1 := mul_nonneg ha ht₁0
          have hn2 := mul_nonneg hb ht₂0
          have hat1 : a * t₁ = 0 := by linarith
          have hbt2 : b * t₂ = 0 := by linarith
          refine ⟨0, 0, le_rfl, zero_le_one, by simp [PosQuad], ?_⟩
          ext coord
          · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, sub_zero, one_mul, zero_mul, add_zero]
            have h1 : a * (1 - t₁) + b * (1 - t₂) = 1 := by linarith
            have h2 : a * t₁ * r₁ coord = 0 := by rw [hat1, zero_mul]
            have h3 : b * t₂ * r₂ coord = 0 := by rw [hbt2, zero_mul]
            linear_combination (q coord) * h1 + h2 + h3
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
          let r := ((a * t₁) / t) • r₁ + ((b * t₂) / t) • r₂
          have hrQ : r ∈ PosQuad := hQconv hr₁ hr₂ (div_nonneg (mul_nonneg ha ht₁0) htpos.le)
            (div_nonneg (mul_nonneg hb ht₂0) htpos.le) (by rw [← add_div]; exact div_self htpos.ne')
          refine ⟨t, r, ht0, ht1, hrQ, ?_⟩
          ext coord
          simp only [r, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          have e1 : t * (a * t₁ / t * r₁ coord) = a * t₁ * r₁ coord := by field_simp
          have e2 : t * (b * t₂ / t * r₂ coord) = b * t₂ * r₂ coord := by field_simp
          rw [mul_add t (a * t₁ / t * r₁ coord) (b * t₂ / t * r₂ coord), e1, e2]
          have hb' : b = 1 - a := by linarith
          simp only [t]; rw [hb']; ring
    exact hsub hp
  · rintro ⟨t, r, ht0, ht1, hrQ, rfl⟩
    exact convex_convexHull ℝ (PosQuad ∪ {q})
      (subset_convexHull ℝ _ (Set.mem_union_right _ rfl))
      (subset_convexHull ℝ _ (Set.mem_union_left _ hrQ))
      (sub_nonneg.mpr ht1) ht0 (by ring)

/-- Rotated coordinates `(ξ, η) = (u - v, u + v)` turning `PosQuad` into `{η ≥ |ξ|}`. -/
noncomputable def rot2 : (ℝ^2) ≃ₗ[ℝ] (ℝ^2) :=
  { toFun := fun p => !₂[p 0 - p 1, p 0 + p 1]
    invFun := fun w => !₂[(w 0 + w 1) / 2, (w 1 - w 0) / 2]
    left_inv := fun p => by ext k; fin_cases k <;> simp <;> ring
    right_inv := fun w => by ext k; fin_cases k <;> simp <;> ring
    map_add' := fun p q => by ext k; fin_cases k <;> simp <;> ring
    map_smul' := fun r p => by ext k; fin_cases k <;> simp <;> ring }

lemma rot2_orient2 (a b c : ℝ^2) : orient2 (rot2 a) (rot2 b) (rot2 c) = 2 * orient2 a b c := by
  simp only [rot2, orient2, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

lemma orthant_cups_caps (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (X : Finset (ℝ^3))
    (hfree : IsCFree PosOctant X)
    (hproj_disj : ∀ i : Fin 3, ∀ x ∈ X, proj3 i x ∉ PosQuad)
    (hproj_inj : ∀ i : Fin 3, Set.InjOn (proj3 i) (X : Set (ℝ^3)))
    (hproj_gp : ∀ i : Fin 3, IsGP2 (X.image (proj3 i)))
    (hcoord_inj : ∀ k : Fin 3, Set.InjOn (fun x : ℝ^3 => x k) (X : Set (ℝ^3)))
    (hcard : (Nat.choose (a + b - 4) (a - 2)) ^ 3 < X.card) :
    (∃ K ⊆ X, K.card = a ∧ IsCCap PosOctant K) ∨ Erdos651.HasConvexSubset b X := by
  classical
  -- Define 3 partial orders R i x y ↔ proj3 i x ∈ convexHull ℝ (PosQuad ∪ {proj3 i y}).
  let R (i : Fin 3) (x y : ℝ^3) : Prop :=
    proj3 i x ∈ convexHull ℝ (PosQuad ∪ {proj3 i y})
  have hrefl : ∀ i x, R i x x := fun i x =>
    subset_convexHull ℝ _ (Set.mem_union_right _ rfl)
  have htrans : ∀ i x y z, R i x y → R i y z → R i x z := fun i x y z hxy hyz => by
    have hsub : PosQuad ∪ {proj3 i y} ⊆ convexHull ℝ (PosQuad ∪ {proj3 i z}) := by
      rintro w (hwQ | rfl)
      · exact subset_convexHull ℝ _ (Set.mem_union_left _ hwQ)
      · exact hyz
    exact convexHull_min hsub (convex_convexHull ℝ _) hxy
  have hanti_on : ∀ i, ∀ x ∈ X, ∀ y ∈ X, R i x y → R i y x → x = y := by
    intro i x hx y hy hxy hyx
    apply hproj_inj i hx hy
    by_contra hne
    obtain ⟨t₁, r₁, ht₁0, ht₁1, hr₁, heq₁⟩ := mem_convexHull_posQuad_insert.mp hxy
    obtain ⟨t₂, r₂, ht₂0, ht₂1, hr₂, heq₂⟩ := mem_convexHull_posQuad_insert.mp hyx
    have ht₁_pos : 0 < t₁ := by
      rcases lt_or_eq_of_le ht₁0 with hp | hz
      · exact hp
      · rw [← hz, sub_zero, one_smul, zero_smul, add_zero] at heq₁; exact (hne heq₁).elim
    have hdenom : 0 < 1 - (1 - t₁) * (1 - t₂) := by nlinarith
    have hxQ : proj3 i x ∈ PosQuad := by
      have hcoord : ∀ c : Fin 2, 0 ≤ proj3 i x c := fun c => by
        have h1 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq₁) c
        have h2 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq₂) c
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2
        have hr1c : 0 ≤ r₁ c := by fin_cases c; exact hr₁.1; exact hr₁.2
        have hr2c : 0 ≤ r₂ c := by fin_cases c; exact hr₂.1; exact hr₂.2
        have key : (1 - (1 - t₁) * (1 - t₂)) * proj3 i x c =
            (1 - t₁) * t₂ * r₂ c + t₁ * r₁ c := by linear_combination h1 + (1 - t₁) * h2
        have hrhs : 0 ≤ (1 - t₁) * t₂ * r₂ c + t₁ * r₁ c :=
          add_nonneg (mul_nonneg (mul_nonneg (by linarith) ht₂0) hr2c) (mul_nonneg ht₁0 hr1c)
        by_contra hneg; push_neg at hneg
        have := mul_neg_of_pos_of_neg hdenom hneg
        linarith
      exact ⟨hcoord 0, hcoord 1⟩
    exact hproj_disj i x hx hxQ
  -- Restrict to subtype ↥X so antisymmetry holds globally for `three_posets_antichain`!
  let Rsub (i : Fin 3) (x y : ↥X) : Prop := R i x.val y.val
  have hincomp : ∀ x ∈ (Finset.univ : Finset ↥X), ∀ y ∈ (Finset.univ : Finset ↥X), x ≠ y →
      ∃ i : Fin 3, ¬ Rsub i x y ∧ ¬ Rsub i y x := by
    intro x _ y _ hxy
    have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    have hline : ∀ t : ℝ, ¬ (0 ≤ x.val 0 + t * (y.val 0 - x.val 0) ∧
        0 ≤ x.val 1 + t * (y.val 1 - x.val 1) ∧ 0 ≤ x.val 2 + t * (y.val 2 - x.val 2)) := by
      intro t ht
      apply hfree x.val x.prop y.val y.prop hxy' t
      refine ⟨?_, ?_, ?_⟩ <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> linarith
    have hhelly := helly_1d_three (x.val 0) (y.val 0 - x.val 0)
      (x.val 1) (y.val 1 - x.val 1) (x.val 2) (y.val 2 - x.val 2) hline
    have hdisj_to_incomp : ∀ i : Fin 3,
        (∀ t : ℝ, (1 - t) • proj3 i x.val + t • proj3 i y.val ∉ PosQuad) →
        ¬ Rsub i x y ∧ ¬ Rsub i y x := by
      intro i hno
      constructor
      · intro hR
        obtain ⟨t, r, ht0, ht1, hrQ, heq⟩ := mem_convexHull_posQuad_insert.mp hR
        have htpos : 0 < t := by
          rcases lt_or_eq_of_le ht0 with hp | hz
          · exact hp
          · rw [← hz, sub_zero, one_smul, zero_smul, add_zero] at heq
            exact (hxy' (hproj_inj i x.prop y.prop heq)).elim
        -- r = (1/t) • proj3 i x + (1 - 1/t) • proj3 i y ∈ PosQuad!
        apply hno (1 - 1 / t)
        have hreq : (1 - (1 - 1 / t)) • proj3 i x.val + (1 - 1 / t) • proj3 i y.val = r := by
          rw [heq]; ext c; fin_cases c <;>
          · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp [htpos.ne']; ring
        rwa [hreq]
      · intro hR
        obtain ⟨t, r, ht0, ht1, hrQ, heq⟩ := mem_convexHull_posQuad_insert.mp hR
        have htpos : 0 < t := by
          rcases lt_or_eq_of_le ht0 with hp | hz
          · exact hp
          · rw [← hz, sub_zero, one_smul, zero_smul, add_zero] at heq
            exact (hxy' (hproj_inj i y.prop x.prop heq).symm).elim
        apply hno (1 / t)
        have hreq : (1 - 1 / t) • proj3 i x.val + (1 / t) • proj3 i y.val = r := by
          rw [heq]; ext c; fin_cases c <;>
          · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp [htpos.ne']; ring
        rwa [hreq]
    rcases hhelly with h0 | h1 | h2
    · refine ⟨0, hdisj_to_incomp 0 fun t ht => h0 t ?_⟩
      simp only [proj3, PosQuad, Set.mem_setOf_eq, LinearMap.coe_mk, AddHom.coe_mk,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at ht
      exact ⟨by linarith, by linarith⟩
    · refine ⟨1, hdisj_to_incomp 1 fun t ht => h1 t ?_⟩
      simp only [proj3, PosQuad, Set.mem_setOf_eq, LinearMap.coe_mk, AddHom.coe_mk,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at ht
      exact ⟨by linarith, by linarith⟩
    · refine ⟨2, hdisj_to_incomp 2 fun t ht => h2 t ?_⟩
      simp only [proj3, PosQuad, Set.mem_setOf_eq, LinearMap.coe_mk, AddHom.coe_mk,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at ht
      exact ⟨by linarith, by linarith⟩
  have hcard' : (Nat.choose (a + b - 4) (a - 2)) ^ 3 < (Finset.univ : Finset ↥X).card := by
    simpa [Finset.card_univ, Fintype.card_coe] using hcard
  obtain ⟨i, Asub, _, hAanti, hAcard⟩ := three_posets_antichain Rsub
    (fun i x => hrefl i x.val) (fun i x y z => htrans i x.val y.val z.val)
    (fun i x y h1 h2 => Subtype.ext (hanti_on i x.val x.prop y.val y.prop h1 h2))
    Finset.univ hincomp (Nat.choose (a + b - 4) (a - 2)) hcard'
  let A : Finset (ℝ^3) := Asub.image Subtype.val
  have hAX : A ⊆ X := fun x hx => by obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx; exact y.prop
  have hAcard_eq : A.card = Asub.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hAanti' : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ R i x y := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    exact hAanti x' hx' y' hy' (fun h => hxy (congrArg Subtype.val h))
  -- Map `A` to `P := A.image (rot2 ∘ proj3 i)` in `ℝ^2`!
  let L : (ℝ^3) →ₗ[ℝ] (ℝ^2) := rot2.toLinearMap.comp (proj3 i)
  have hL_inj : Set.InjOn L (A : Set (ℝ^3)) :=
    (rot2.injective.injOn).comp (hproj_inj i |>.mono hAX) (Set.mapsTo_image _ _)
  let P : Finset (ℝ^2) := A.image L
  have hPcard : Nat.choose (a + b - 4) (a - 2) < P.card := by
    rw [Finset.card_image_of_injOn hL_inj, hAcard_eq]; exact hAcard
  -- Helper: adding `(δ, δ)` with `δ > 0` to `p` stays inside `convexHull (PosQuad ∪ {p})`!
  have hadd_pos : ∀ p q : ℝ^2, p 0 < q 0 → p 1 < q 1 → q ∈ convexHull ℝ (PosQuad ∪ {p}) := by
    intro p q h0 h1
    let d0 := q 0 - p 0
    let d1 := q 1 - p 1
    have hd0 : 0 < d0 := sub_pos.mpr h0
    have hd1 : 0 < d1 := sub_pos.mpr h1
    -- Pick t ∈ (0, 1) so p 0 + d0 / t ≥ 0 and p 1 + d1 / t ≥ 0!
    let Mbig : ℝ := max 1 (max (-p 0 / d0) (-p 1 / d1)) + 1
    have hMpos : 1 < Mbig := by dsimp only [Mbig]; linarith [le_max_left 1 (max (-p 0 / d0) (-p 1 / d1))]
    let t := 1 / Mbig
    have ht0 : 0 < t := div_pos zero_lt_one (by linarith)
    have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; exact hMpos.le
    let r : ℝ^2 := !₂[p 0 + Mbig * d0, p 1 + Mbig * d1]
    have hrQ : r ∈ PosQuad := by
      simp only [PosQuad, r, Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have hM1 : -p 0 / d0 ≤ Mbig := by
        dsimp only [Mbig]; linarith [le_max_right 1 (max (-p 0 / d0) (-p 1 / d1)), le_max_left (-p 0 / d0) (-p 1 / d1)]
      have hM2 : -p 1 / d1 ≤ Mbig := by
        dsimp only [Mbig]; linarith [le_max_right 1 (max (-p 0 / d0) (-p 1 / d1)), le_max_right (-p 0 / d0) (-p 1 / d1)]
      exact ⟨by have := (div_le_iff₀ hd0).mp hM1; linarith,
             by have := (div_le_iff₀ hd1).mp hM2; linarith⟩
    refine mem_convexHull_posQuad_insert.mpr ⟨t, r, ht0.le, ht1, hrQ, ?_⟩
    ext k; fin_cases k <;>
    · simp only [r, t, d0, d1, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      field_simp [(by linarith : Mbig ≠ 0)]
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      ring
  -- Distinct ξ-coordinates on P (because equal ξ means `u₂ - u₁ = v₂ - v₁ ≠ 0`, contradicting antichain!)
  have hdxP : DistinctX2 P := by
    intro w₁ hw₁ w₂ hw₂ hne heq
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
    obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
    have hxne : x₁ ≠ x₂ := fun h => hne (by subst h; rfl)
    have hdiff : proj3 i x₁ 0 - proj3 i x₁ 1 = proj3 i x₂ 0 - proj3 i x₂ 1 := by
      simpa [L, rot2] using heq
    have h0ne : proj3 i x₁ 0 ≠ proj3 i x₂ 0 := by
      fin_cases i
      · exact fun h => hxne (hcoord_inj 1 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
      · exact fun h => hxne (hcoord_inj 0 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
      · exact fun h => hxne (hcoord_inj 0 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
    rcases lt_or_gt_of_ne h0ne with hlt | hgt
    · exact hAanti' x₂ hx₂ x₁ hx₁ hxne.symm (hadd_pos _ _ hlt (by linarith))
    · exact hAanti' x₁ hx₁ x₂ hx₂ hxne (hadd_pos _ _ hgt (by linarith))
  have hgpP : IsGP2 P := by
    intro w₁ hw₁ w₂ hw₂ w₃ hw₃ h12 h23 h13
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
    obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
    obtain ⟨x₃, hx₃, rfl⟩ := Finset.mem_image.mp hw₃
    dsimp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [rot2_orient2]
    have hp12 : proj3 i x₁ ≠ proj3 i x₂ := fun h => h12 (by simp [L, h])
    have hp23 : proj3 i x₂ ≠ proj3 i x₃ := fun h => h23 (by simp [L, h])
    have hp13 : proj3 i x₁ ≠ proj3 i x₃ := fun h => h13 (by simp [L, h])
    have hnz := hproj_gp i _ (Finset.mem_image_of_mem _ (hAX hx₁))
      _ (Finset.mem_image_of_mem _ (hAX hx₂)) _ (Finset.mem_image_of_mem _ (hAX hx₃)) hp12 hp23 hp13
    exact mul_ne_zero two_ne_zero hnz
  -- Apply 2D Erdős-Szekeres to `P`!
  rcases erdos_szekeres_cups_caps a b ha hb P hdxP hgpP hPcard with
    ⟨l, hlen, hlP, hcup⟩ | ⟨l, hlen, hlP, hcap⟩
  · -- Case 1: `a`-cup `l` in `P` → lifts to a `PosOctant`-cap `K` of size `a` in `A ⊆ X`!
    left
    -- For every pair in `P` with `w₁ 0 < w₂ 0`, `-1 < slope2 w₁ w₂ < 1`!
    have hsl_bnd : ∀ w₁ ∈ P, ∀ w₂ ∈ P, w₁ 0 < w₂ 0 → -1 < slope2 w₁ w₂ ∧ slope2 w₁ w₂ < 1 := by
      intro w₁ hw₁ w₂ hw₂ hlt
      obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
      have hxne : x₁ ≠ x₂ := fun h => by subst h; exact lt_irrefl _ hlt
      have h0ne : proj3 i x₁ 0 ≠ proj3 i x₂ 0 := by
        fin_cases i
        · exact fun h => hxne (hcoord_inj 1 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
        · exact fun h => hxne (hcoord_inj 0 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
        · exact fun h => hxne (hcoord_inj 0 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
      have h1ne : proj3 i x₁ 1 ≠ proj3 i x₂ 1 := by
        fin_cases i
        · exact fun h => hxne (hcoord_inj 2 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
        · exact fun h => hxne (hcoord_inj 2 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
        · exact fun h => hxne (hcoord_inj 1 (hAX hx₁) (hAX hx₂) (by simpa [proj3] using h))
      have hdx : 0 < L x₂ 0 - L x₁ 0 := sub_pos.mpr hlt
      simp only [L, rot2, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, PiLp.toLp_apply, WithLp.ofLp_toLp] at hdx
      rw [slope2]
      simp only [L, rot2, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, PiLp.toLp_apply, WithLp.ofLp_toLp]
      rw [lt_div_iff₀ hdx, div_lt_iff₀ hdx]
      constructor
      · by_contra hle; push_neg at hle
        -- (u₂ - u₁) + (v₂ - v₁) ≤ -((u₂ - u₁) - (v₂ - v₁)) ⇒ u₂ ≤ u₁; since u₁ ≠ u₂, u₂ < u₁;
        -- and hdx > 0 ⇒ v₂ < v₁ ⇒ x₁ ∈ conv(PosQuad ∪ {x₂}), contradiction!
        have hu : proj3 i x₂ 0 < proj3 i x₁ 0 := lt_of_le_of_ne (by linarith) h0ne.symm
        have hv : proj3 i x₂ 1 < proj3 i x₁ 1 := by linarith
        exact hAanti' x₁ hx₁ x₂ hx₂ hxne (hadd_pos _ _ hu hv)
      · by_contra hge; push_neg at hge
        -- (u₂ - u₁) + (v₂ - v₁) ≥ (u₂ - u₁) - (v₂ - v₁) ⇒ v₁ ≤ v₂ ⇒ v₁ < v₂, and hdx > 0 ⇒ u₁ < u₂!
        have hv : proj3 i x₁ 1 < proj3 i x₂ 1 := lt_of_le_of_ne (by linarith) h1ne
        have hu : proj3 i x₁ 0 < proj3 i x₂ 0 := by linarith
        exact hAanti' x₂ hx₂ x₁ hx₁ hxne.symm (hadd_pos _ _ hu hv)
    -- Every `w ∈ P` has `w 1 < |w 0|` (since `proj3 i x ∉ PosQuad`!).
    have hw_out : ∀ w ∈ P, w 1 < |w 0| := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      have hnotQ := hproj_disj i x (hAX hx)
      simp only [PosQuad, Set.mem_setOf_eq, not_and_or, not_le] at hnotQ
      simp only [L, rot2, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rcases hnotQ with h0 | h1
      · have := neg_le_abs (proj3 i x 0 - proj3 i x 1); linarith
      · have := le_abs_self (proj3 i x 0 - proj3 i x 1); linarith
    -- Helper: for any `w₁, w₂ ∈ P` with `0 < w₁ 0 < w₂ 0`, `w₁ 1 / w₁ 0 < slope2 w₁ w₂`!
    have hray_pos : ∀ w₁ ∈ P, ∀ w₂ ∈ P, 0 < w₁ 0 → w₁ 0 < w₂ 0 → w₁ 1 / w₁ 0 < slope2 w₁ w₂ := by
      intro w₁ hw₁ w₂ hw₂ h0pos hlt
      by_contra hle; push_neg at hle
      obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
      have hxne : x₁ ≠ x₂ := fun h => by subst h; exact lt_irrefl _ hlt
      -- Let t := 1 - L x₁ 0 / L x₂ 0 ∈ (0, 1). Then `(1 - t) • L x₂ + t • 0` has ξ = L x₁ 0 and η ≥ L x₁ 1!
      have h2pos : 0 < L x₂ 0 := h0pos.trans hlt
      let lamq := L x₁ 0 / L x₂ 0
      have hlam0 : 0 < lamq := div_pos h0pos h2pos
      have hlam1 : lamq < 1 := (div_lt_one h2pos).mpr hlt
      have hdx : 0 < L x₂ 0 - L x₁ 0 := sub_pos.mpr hlt
      rw [slope2, div_le_div_iff₀ hdx h0pos] at hle
      -- So L x₂ 1 * L x₁ 0 ≤ L x₁ 1 * L x₂ 0, i.e., lamq * L x₂ 1 ≤ L x₁ 1!
      have hη_le : lamq * L x₂ 1 ≤ L x₁ 1 := by
        dsimp only [lamq]; rw [div_mul_eq_mul_div, div_le_iff₀ h2pos]; linarith
      -- Thus L x₁ = lamq • L x₂ + (0, L x₁ 1 - lamq * L x₂ 1), and `(0, δ) = rot2 (δ/2, δ/2)` with δ ≥ 0!
      let δ := L x₁ 1 - lamq * L x₂ 1
      have hδ : 0 ≤ δ := sub_nonneg.mpr hη_le
      let r : ℝ^2 := !₂[δ / (2 * (1 - lamq)), δ / (2 * (1 - lamq))]
      have hrQ : r ∈ PosQuad := by
        have h1m : 0 < 2 * (1 - lamq) := by linarith
        exact ⟨div_nonneg hδ h1m.le, div_nonneg hδ h1m.le⟩
      have heq : proj3 i x₁ = (1 - (1 - lamq)) • proj3 i x₂ + (1 - lamq) • r := by
        apply rot2.injective
        rw [map_add, map_smul, map_smul]
        ext k; fin_cases k
        · change L x₁ 0 = (1 - (1 - lamq)) * L x₂ 0 + (1 - lamq) * (rot2 r) 0
          simp only [rot2, r, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_self, mul_zero, add_zero]
          dsimp only [lamq]; field_simp [h2pos.ne']; ring
        · change L x₁ 1 = (1 - (1 - lamq)) * L x₂ 1 + (1 - lamq) * (rot2 r) 1
          simp only [rot2, r, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          have h1m : 1 - lamq ≠ 0 := by linarith
          dsimp only [δ]; field_simp [h1m]; ring
      exact hAanti' x₁ hx₁ x₂ hx₂ hxne
        (mem_convexHull_posQuad_insert.mpr ⟨1 - lamq, r, by linarith, by linarith, hrQ, heq⟩)
    -- Symmetric helper: for `w₁, w₂ ∈ P` with `w₁ 0 < w₂ 0 < 0`, `slope2 w₁ w₂ < w₂ 1 / w₂ 0`!
    have hray_neg : ∀ w₁ ∈ P, ∀ w₂ ∈ P, w₁ 0 < w₂ 0 → w₂ 0 < 0 → slope2 w₁ w₂ < w₂ 1 / w₂ 0 := by
      intro w₁ hw₁ w₂ hw₂ hlt h0neg
      by_contra hge; push_neg at hge
      obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
      have hxne : x₁ ≠ x₂ := fun h => by subst h; exact lt_irrefl _ hlt
      have h1neg : L x₁ 0 < 0 := hlt.trans h0neg
      let lamq := L x₂ 0 / L x₁ 0
      have hlam0 : 0 < lamq := div_pos_of_neg_of_neg h0neg h1neg
      have hlam1 : lamq < 1 := by
        rw [div_lt_one_of_neg h1neg]; exact hlt
      have hdx : 0 < L x₂ 0 - L x₁ 0 := sub_pos.mpr hlt
      rw [slope2] at hge
      have hη_le : lamq * L x₁ 1 ≤ L x₂ 1 := by
        have h1 : (L x₂ 1 / L x₂ 0) * (L x₂ 0 - L x₁ 0) ≤ L x₂ 1 - L x₁ 1 := (le_div_iff₀ hdx).mp hge
        have h2 : L x₂ 1 * (L x₂ 0 - L x₁ 0) ≥ (L x₂ 1 - L x₁ 1) * L x₂ 0 := by
          have := mul_le_mul_of_nonpos_right h1 h0neg.le
          have hmul : (L x₂ 1 / L x₂ 0) * (L x₂ 0 - L x₁ 0) * L x₂ 0 =
              L x₂ 1 * (L x₂ 0 - L x₁ 0) := by field_simp [h0neg.ne] <;> ring
          linarith
        have h3 : L x₁ 1 * L x₂ 0 ≥ L x₂ 1 * L x₁ 0 := by linarith
        dsimp only [lamq]; rw [div_mul_eq_mul_div, div_le_iff_of_neg h1neg]; linarith
      let δ := L x₂ 1 - lamq * L x₁ 1
      have hδ : 0 ≤ δ := sub_nonneg.mpr hη_le
      let r : ℝ^2 := !₂[δ / (2 * (1 - lamq)), δ / (2 * (1 - lamq))]
      have hrQ : r ∈ PosQuad := by
        have h1m : 0 < 2 * (1 - lamq) := by linarith
        exact ⟨div_nonneg hδ h1m.le, div_nonneg hδ h1m.le⟩
      have heq : proj3 i x₂ = (1 - (1 - lamq)) • proj3 i x₁ + (1 - lamq) • r := by
        apply rot2.injective
        rw [map_add, map_smul, map_smul]
        ext k; fin_cases k
        · change L x₂ 0 = (1 - (1 - lamq)) * L x₁ 0 + (1 - lamq) * (rot2 r) 0
          simp only [rot2, r, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_self, mul_zero, add_zero]
          dsimp only [lamq]; field_simp [h1neg.ne] <;> ring
        · change L x₂ 1 = (1 - (1 - lamq)) * L x₁ 1 + (1 - lamq) * (rot2 r) 1
          simp only [rot2, r, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          have h1m : 1 - lamq ≠ 0 := by linarith
          dsimp only [δ]; field_simp [h1m]; ring
      exact hAanti' x₂ hx₂ x₁ hx₁ hxne.symm
        (mem_convexHull_posQuad_insert.mpr ⟨1 - lamq, r, by linarith, by linarith, hrQ, heq⟩)
    -- Lift `l.toFinset ⊆ P = A.image L` back to `K ⊆ A ⊆ X`!
    let K : Finset (ℝ^3) := A.filter (fun x => L x ∈ l.toFinset)
    have hKA : K ⊆ A := Finset.filter_subset _ _
    have hKL : K.image L = l.toFinset := by
      ext w
      constructor
      · intro hw; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw; exact (Finset.mem_filter.mp hx).2
      · intro hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hlP w (List.mem_toFinset.mp hw))
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hw⟩, rfl⟩
    have hKcard : K.card = a := by
      rw [← Finset.card_image_of_injOn (hL_inj.mono hKA), hKL,
          List.toFinset_card_of_nodup (isCup2_nodup hcup), hlen]
    refine ⟨K, hKA.trans hAX, hKcard, fun x hxK hmem => ?_⟩
    have hLx_mem : L x ∈ l := List.mem_toFinset.mp (Finset.mem_filter.mp hxK).2
    obtain ⟨r, hr, hLr⟩ := List.mem_iff_getElem.mp hLx_mem
    -- Find slope `m ∈ [-1, 1]` with `l[r] 1 < m * l[r] 0` and separating `l[r]` from all `l[j]` (`j ≠ r`)!
    let lo : ℝ := if hr0 : r = 0 then -1 else slope2 (l[r - 1]'(by omega)) (l[r]'hr)
    let hi : ℝ := if hrl : r + 1 < l.length then slope2 (l[r]'hr) (l[r + 1]'hrl) else 1
    have hlo_ge : -1 ≤ lo := by
      dsimp only [lo]; split_ifs with hr0
      · exact le_rfl
      · exact (hsl_bnd _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
          (hcup.1 (r - 1) r (by omega) hr (by omega))).1.le
    have hhi_le : hi ≤ 1 := by
      dsimp only [hi]; split_ifs with hrl
      · exact (hsl_bnd _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
          (hcup.1 r (r + 1) hr hrl (by omega))).2.le
      · exact le_rfl
    have hlo_lt_hi : lo < hi := by
      dsimp only [lo, hi]
      split_ifs with hr0 hrl hrl
      · exact (hsl_bnd _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
          (hcup.1 r (r + 1) hr hrl (by omega))).1
      · norm_num
      · have h := isCup2_slope_adj_mono hcup (i := r - 1) (j := r) (by omega) hrl
        have hr1 : r - 1 + 1 = r := by omega
        simpa [hr1] using h
      · exact (hsl_bnd _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
          (hcup.1 (r - 1) r (by omega) hr (by omega))).2
    have hm_ex : ∃ m : ℝ, -1 ≤ m ∧ m ≤ 1 ∧ lo < m ∧ m < hi ∧ l[r] 1 < m * l[r] 0 := by
      rcases lt_trichotomy (l[r] 0) 0 with hneg | hzero | hpos
      · -- ξ_r < 0 ⇒ need m < η_r / ξ_r
        have hbound : l[r] 1 / l[r] 0 > -1 := by
          have hout := hw_out l[r] (hlP _ (List.getElem_mem _))
          rw [abs_of_neg hneg] at hout
          rw [gt_iff_lt, lt_div_iff_of_neg hneg]; linarith
        have hlo_lt_ray : lo < l[r] 1 / l[r] 0 := by
          dsimp only [lo]; split_ifs with hr0
          · exact hbound
          · exact hray_neg _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
              (hcup.1 (r - 1) r (by omega) hr (by omega)) hneg
        let hi' := min hi (l[r] 1 / l[r] 0)
        have hlt' : lo < hi' := lt_min hlo_lt_hi hlo_lt_ray
        refine ⟨(lo + hi') / 2, by linarith, by linarith [min_le_left hi (l[r] 1 / l[r] 0)],
          by linarith, by linarith [min_le_left hi (l[r] 1 / l[r] 0)], ?_⟩
        have hmlt : (lo + hi') / 2 < l[r] 1 / l[r] 0 := by linarith [min_le_right hi (l[r] 1 / l[r] 0)]
        have := (lt_div_iff_of_neg hneg).mp hmlt
        linarith
      · -- ξ_r = 0 ⇒ η_r < 0 = m * 0 for any m!
        have hout := hw_out l[r] (hlP _ (List.getElem_mem _))
        rw [hzero, abs_zero] at hout
        exact ⟨(lo + hi) / 2, by linarith, by linarith, by linarith, by linarith, by rw [hzero, mul_zero]; exact hout⟩
      · -- ξ_r > 0 ⇒ need η_r / ξ_r < m
        have hbound : l[r] 1 / l[r] 0 < 1 := by
          have hout := hw_out l[r] (hlP _ (List.getElem_mem _))
          rw [abs_of_pos hpos] at hout
          rw [div_lt_one hpos]; exact hout
        have hray_lt_hi : l[r] 1 / l[r] 0 < hi := by
          dsimp only [hi]; split_ifs with hrl
          · exact hray_pos _ (hlP _ (List.getElem_mem _)) _ (hlP _ (List.getElem_mem _))
              hpos (hcup.1 r (r + 1) hr hrl (by omega))
          · exact hbound
        let lo' := max lo (l[r] 1 / l[r] 0)
        have hlt' : lo' < hi := max_lt hlo_lt_hi hray_lt_hi
        refine ⟨(lo' + hi) / 2, by linarith [le_max_left lo (l[r] 1 / l[r] 0)], by linarith,
          by linarith [le_max_left lo (l[r] 1 / l[r] 0)], by linarith, ?_⟩
        have hmgt : l[r] 1 / l[r] 0 < (lo' + hi) / 2 := by linarith [le_max_right lo (l[r] 1 / l[r] 0)]
        have := (div_lt_iff₀ hpos).mp hmgt
        linarith
    obtain ⟨m, hm1, hm2, hmlo, hmhi, hm0⟩ := hm_ex
    let f : (ℝ^3) →ₗ[ℝ] ℝ :=
      { toFun := fun u => L u 1 - m * L u 0
        map_add' := fun u v => by simp [map_add]; ring
        map_smul' := fun c u => by simp [map_smul]; ring }
    let c := f x
    have habove : ∀ y ∈ PosOctant ∪ ((K.erase x : Finset (ℝ^3)) : Set (ℝ^3)), c < f y := by
      rintro y (hyQ | hyK)
      · have hpyQ : proj3 i y ∈ PosQuad := proj3_posOctant i hyQ
        have hLy : |L y 0| ≤ L y 1 := by
          simp only [L, rot2, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk,
            LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [abs_le]; exact ⟨by linarith [hpyQ.1, hpyQ.2], by linarith [hpyQ.1, hpyQ.2]⟩
        have hmy : m * L y 0 ≤ |L y 0| := by
          rcases le_or_gt 0 (L y 0) with hnn | hng
          · rw [abs_of_nonneg hnn]; nlinarith
          · rw [abs_of_neg hng]; nlinarith
        have hfx : f x < 0 := by
          simp only [f, LinearMap.coe_mk, AddHom.coe_mk, ← hLr]; linarith
        have hfy : 0 ≤ f y := by
          simp only [f, LinearMap.coe_mk, AddHom.coe_mk]; linarith
        linarith
      · have hyK' := Finset.mem_erase.mp (Finset.mem_coe.mp hyK)
        have hLy_mem : L y ∈ l := List.mem_toFinset.mp (Finset.mem_filter.mp hyK'.2).2
        obtain ⟨j, hj, hLj⟩ := List.mem_iff_getElem.mp hLy_mem
        have hjr : j ≠ r := fun heq => hyK'.1 (hL_inj (hKA hyK'.2) (hKA hxK) (by subst heq; exact hLj.symm.trans hLr))
        rcases lt_or_gt_of_ne hjr with hlt | hgt
        · have hr0 : r ≠ 0 := by omega
          have hsl_le : slope2 l[j] l[r] ≤ lo := by
            dsimp only [lo]; rw [dif_neg hr0]; exact isCup2_slope_gt_left hcup hlt hr
          have hdx : 0 < l[r] 0 - l[j] 0 := sub_pos.mpr (hcup.1 j r hj hr hlt)
          have hsl : slope2 l[j] l[r] < m := hsl_le.trans_lt hmlo
          rw [slope2, div_lt_iff₀ hdx] at hsl
          simp only [c, f, LinearMap.coe_mk, AddHom.coe_mk, ← hLr, ← hLj]; linarith
        · have hrl : r + 1 < l.length := by omega
          have hsl_ge : hi ≤ slope2 l[r] l[j] := by
            dsimp only [hi]; rw [dif_pos hrl]; exact isCup2_slope_ge_right hcup hgt hj
          have hdx : 0 < l[j] 0 - l[r] 0 := sub_pos.mpr (hcup.1 r j hr hj hgt)
          have hsl : m < slope2 l[r] l[j] := hmhi.trans_le hsl_ge
          rw [slope2, lt_div_iff₀ hdx] at hsl
          simp only [c, f, LinearMap.coe_mk, AddHom.coe_mk, ← hLr, ← hLj]; linarith
    have hconv : Convex ℝ {u : ℝ^3 | c < f u} := convex_halfSpace_gt f.isLinear c
    exact lt_irrefl c (hconv.convexHull_subset_iff.mpr habove hmem)
  · -- Case 2: `b`-cap `l` in `P = A.image L` → lifts to `HasConvexSubset b X`!
    right
    have hnodup : l.Nodup := by
      rw [List.nodup_iff_injective_getElem]
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have := hcap.1 i.val j.val i.isLt j.isLt hlt; simp only at hij; rw [hij] at this; exact lt_irrefl _ this
      · have := hcap.1 j.val i.val j.isLt i.isLt hgt; simp only at hij; rw [hij] at this; exact lt_irrefl _ this
    have hconv2 : Erdos651.HasConvexSubset b (A.image L) :=
      ⟨l.toFinset, fun w hw => hlP w (List.mem_toFinset.mp hw),
       by rw [List.toFinset_card_of_nodup hnodup, hlen], isCap2_convexIndependent hcap⟩
    -- Lift convex subset from `A.image L` to `A` to `X`!
    obtain ⟨Z, hZ, hZcard, hZconv⟩ := hconv2
    let Y := A.filter (fun x => L x ∈ Z)
    have hYA : Y ⊆ A := Finset.filter_subset _ _
    have hYL : Y.image L = Z := by
      ext w
      constructor
      · intro hw; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw; exact (Finset.mem_filter.mp hx).2
      · intro hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hZ hw)
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hw⟩, rfl⟩
    refine ⟨Y, hYA.trans hAX, ?_, ?_⟩
    · rw [← Finset.card_image_of_injOn (hL_inj.mono hYA), hYL, hZcard]
    · rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hZconv ⊢
      intro y hy hmem
      have hLy : L y ∈ (Z : Set (ℝ^2)) := by rw [← hYL]; exact Finset.mem_image_of_mem L hy
      apply hZconv (L y) hLy
      have him : L '' ((Y : Set (ℝ^3)) \ {y}) ⊆ (Z : Set (ℝ^2)) \ {L y} := by
        rintro _ ⟨u, ⟨hu, hune⟩, rfl⟩
        exact ⟨by rw [← hYL]; exact Finset.mem_image_of_mem L hu,
               fun heq => hune (hL_inj (hYA hu) (hYA hy) heq)⟩
      exact convexHull_mono him (by rw [← L.image_convexHull]; exact ⟨y, hmem, rfl⟩)

end PZ651

open scoped EuclideanGeometry BigOperators
open Filter

namespace PZ651

/-! ## Section 6: Generic Projection ℝ^3 → ℝ^2 -/

def projXY (x : ℝ^3) : ℝ^2 := !₂[x 0, x 1]

def projXYLinear : (ℝ^3) →ₗ[ℝ] (ℝ^2) :=
  { toFun := projXY
    map_add' := fun x y => by ext k; fin_cases k <;> simp [projXY]
    map_smul' := fun r x => by ext k; fin_cases k <;> simp [projXY] }

lemma linearEquiv_preserves_gp {k : ℕ} (T : (ℝ^k) ≃ₗ[ℝ] (ℝ^k)) {X : Finset (ℝ^k)}
    (hX : Erdos651.IsInGeneralPosition X) :
    Erdos651.IsInGeneralPosition (X.image T) := by
  classical
  intro Z hZ hZcard
  let Y := X.filter (fun x => T x ∈ Z)
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image T = Z := by
    ext z
    constructor
    · intro hz; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz; exact (Finset.mem_filter.mp hx).2
    · intro hz; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have hYcard : Y.card ≤ k + 1 := by
    rwa [← Finset.card_image_of_injective Y T.injective, hYZ]
  have hind := hX Y hYX hYcard
  have hrange : Set.range (T.toAffineEquiv ∘ ((↑) : ↥(Y : Set (ℝ^k)) → ℝ^k)) = (Z : Set (ℝ^k)) := by
    rw [Set.range_comp, Subtype.range_coe]
    change T '' (Y : Set (ℝ^k)) = (Z : Set (ℝ^k))
    rw [← Finset.coe_image, hYZ]
  have hind' : AffineIndependent ℝ (T.toAffineEquiv ∘ ((↑) : ↥(Y : Set (ℝ^k)) → ℝ^k)) :=
    (T.toAffineEquiv.affineIndependent_iff).mpr hind
  rw [← hrange]
  exact hind'.range

lemma linearEquiv_reflects_hasConvexSubset {k n : ℕ} (T : (ℝ^k) ≃ₗ[ℝ] (ℝ^k)) {X : Finset (ℝ^k)}
    (h : Erdos651.HasConvexSubset n (X.image T)) :
    Erdos651.HasConvexSubset n X := by
  classical
  obtain ⟨Z, hZ, hZcard, hZconv⟩ := h
  let Y := X.filter (fun x => T x ∈ Z)
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image T = Z := by
    ext z
    constructor
    · intro hz; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz; exact (Finset.mem_filter.mp hx).2
    · intro hz; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  refine ⟨Y, hYX, ?_, ?_⟩
  · rw [← Finset.card_image_of_injective Y T.injective, hYZ, hZcard]
  · rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hZconv ⊢
    intro y hy hmem
    have hTy : T y ∈ (Z : Set (ℝ^k)) := by rw [← hYZ]; exact Finset.mem_image_of_mem T hy
    apply hZconv (T y) hTy
    have him : T '' ((Y : Set (ℝ^k)) \ {y}) ⊆ (Z : Set (ℝ^k)) \ {T y} := by
      rintro _ ⟨a, ⟨ha, hane⟩, rfl⟩
      exact ⟨by rw [← hYZ]; exact Finset.mem_image_of_mem T ha, fun heq => hane (T.injective heq)⟩
    refine convexHull_mono him ?_
    have himg := T.toLinearMap.image_convexHull ((Y : Set (ℝ^k)) \ {y})
    simp only [LinearEquiv.coe_coe] at himg
    rw [← himg]; exact ⟨y, hmem, rfl⟩

lemma exists_avoid_finite_real (bad : Set ℝ) (hbad : bad.Finite) : ∃ s : ℝ, s ∉ bad := by
  by_contra h
  push_neg at h
  have huniv : (Set.univ : Set ℝ) ⊆ bad := fun x _ => h x
  exact Set.infinite_univ (hbad.subset huniv)

lemma quadratic_zeros_finite {a b c : ℝ} (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    {s : ℝ | a + b * s + c * s ^ 2 = 0}.Finite := by
  let p : Polynomial ℝ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2
  have hp_ne : p ≠ 0 := by
    intro hp0
    have h0 : p.coeff 0 = 0 := by rw [hp0]; simp
    have h1 : p.coeff 1 = 0 := by rw [hp0]; simp
    have h2 : p.coeff 2 = 0 := by rw [hp0]; simp
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_zero, Polynomial.coeff_X, Polynomial.coeff_C_succ,
      mul_one, mul_zero, add_zero, zero_add] at h0 h1 h2
    norm_num at h0 h1 h2
    rcases hne with ha | hb | hc
    · exact ha h0
    · exact hb h1
    · exact hc h2
  have hsub : {s : ℝ | a + b * s + c * s ^ 2 = 0} ⊆ (p.roots.toFinset : Set ℝ) := by
    intro s hs
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot]
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hs
  exact (p.roots.toFinset.finite_toSet).subset hsub

/-- Cross product in `ℝ^3`. -/
def cross3 (u v : ℝ^3) : ℝ^3 :=
  !₂[u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

lemma cross3_ne_zero_of_gp3 {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X)
    {a b c : ℝ^3} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cross3 (b - a) (c - a) ≠ 0 := by
  classical
  intro hzero
  let Y : Finset (ℝ^3) := {a, b, c}
  have hYX : Y ⊆ X := by
    intro x hx; simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hYcard : Y.card ≤ 3 + 1 := by
    calc Y.card ≤ ({b, c} : Finset (ℝ^3)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
      _ ≤ 4 := by omega
  have hind := hX Y hYX hYcard
  have haY : a ∈ Y := Finset.mem_insert_self _ _
  have hbY : b ∈ Y := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcY : c ∈ Y := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥(Y : Set (ℝ^3)) → ℝ^3)
    ⟨a, haY⟩).mp hind
  let ib : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} := ⟨⟨b, hbY⟩, fun h => hab (congrArg Subtype.val h).symm⟩
  let ic : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} := ⟨⟨c, hcY⟩, fun h => hac (congrArg Subtype.val h).symm⟩
  have hibic : ib ≠ ic := fun h => hbc (congrArg (fun z => z.val.val) h)
  have h0 : (b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1) = 0 := by
    have := congrFun (congrArg (fun v : ℝ^3 => (v : Fin 3 → ℝ)) hzero) 0
    simpa [cross3] using this
  have h1 : (b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2) = 0 := by
    have := congrFun (congrArg (fun v : ℝ^3 => (v : Fin 3 → ℝ)) hzero) 1
    simpa [cross3] using this
  have h2 : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
    have := congrFun (congrArg (fun v : ℝ^3 => (v : Fin 3 → ℝ)) hzero) 2
    simpa [cross3] using this
  have hkill : ∀ k : Fin 3, b k - a k = 0 := by
    intro k
    by_contra hbk
    have hcomb : (c k - a k) • (b -ᵥ a) + (-(b k - a k)) • (c -ᵥ a) = 0 := by
      ext j; fin_cases k <;> fin_cases j <;> simp <;> linarith
    have hsum0 : ∑ i : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩},
        (if i = ib then c k - a k else if i = ic then -(b k - a k) else 0) •
          (i.val.val -ᵥ a) = 0 := by
      rw [Finset.sum_eq_add ib ic hibic (fun j _ hj => by simp [hj.1, hj.2])
        (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
      simp only [ite_true, hibic.symm, ite_false]
      exact hcomb
    have hcoef := Fintype.linearIndependent_iff.mp hlin _ hsum0 ic
    simp only [hibic.symm, ite_false, ite_true, neg_eq_zero] at hcoef
    exact hbk hcoef
  apply hab
  ext k; have := hkill k; linarith

lemma generic_projection_3d (X : Finset (ℝ^3)) (hX : Erdos651.IsInGeneralPosition X) :
    ∃ T : (ℝ^3) ≃ₗ[ℝ] (ℝ^3),
      Set.InjOn projXY ((X.image T : Finset (ℝ^3)) : Set (ℝ^3)) ∧
      IsGP2 ((X.image T).image projXY) ∧
      DistinctX2 ((X.image T).image projXY) := by
  classical
  -- Step 1: pick s : ℝ avoiding all bad directions d(s) = (1, s, s^2).
  let badTriples : Set ℝ :=
    ⋃ a ∈ X, ⋃ b ∈ X, ⋃ c ∈ X,
      if a ≠ b ∧ b ≠ c ∧ a ≠ c then
        let w := cross3 (b - a) (c - a)
        {s : ℝ | w 0 + w 1 * s + w 2 * s ^ 2 = 0}
      else ∅
  let badPairs : Set ℝ :=
    ⋃ a ∈ X, ⋃ b ∈ X,
      if a ≠ b then
        {s : ℝ | b 1 - a 1 = s * (b 0 - a 0) ∧ b 2 - a 2 = s ^ 2 * (b 0 - a 0)}
      else ∅
  have hbadT_fin : badTriples.Finite := by
    refine X.finite_toSet.biUnion fun a ha => X.finite_toSet.biUnion fun b hb =>
      X.finite_toSet.biUnion fun c hc => ?_
    split_ifs with hne
    · have hw := cross3_ne_zero_of_gp3 hX ha hb hc hne.1 hne.2.1 hne.2.2
      have hw' : cross3 (b - a) (c - a) 0 ≠ 0 ∨ cross3 (b - a) (c - a) 1 ≠ 0 ∨
          cross3 (b - a) (c - a) 2 ≠ 0 := by
        by_contra hall; push_neg at hall
        apply hw; ext k; fin_cases k <;> simp [hall]
      exact quadratic_zeros_finite hw'
    · exact Set.finite_empty
  have hbadP_fin : badPairs.Finite := by
    refine X.finite_toSet.biUnion fun a ha => X.finite_toSet.biUnion fun b hb => ?_
    split_ifs with hab
    · by_cases h0 : b 0 - a 0 = 0
      · by_cases h1 : b 1 - a 1 = 0
        · have h2 : b 2 - a 2 ≠ 0 := by
            intro h2; apply hab; ext k; fin_cases k <;> simp <;> linarith
          have hemp : {s : ℝ | b 1 - a 1 = s * (b 0 - a 0) ∧ b 2 - a 2 = s ^ 2 * (b 0 - a 0)} = ∅ := by
            ext s; simp [h0, h2]
          rw [hemp]; exact Set.finite_empty
        · have hemp : {s : ℝ | b 1 - a 1 = s * (b 0 - a 0) ∧ b 2 - a 2 = s ^ 2 * (b 0 - a 0)} = ∅ := by
            ext s; simp [h0, h1]
          rw [hemp]; exact Set.finite_empty
      · have hsub : {s : ℝ | b 1 - a 1 = s * (b 0 - a 0) ∧ b 2 - a 2 = s ^ 2 * (b 0 - a 0)} ⊆
            {(b 1 - a 1) / (b 0 - a 0)} := by
          intro s hs; simp only [Set.mem_singleton_iff]
          exact eq_div_of_mul_eq h0 hs.1.symm
        exact (Set.finite_singleton _).subset hsub
    · exact Set.finite_empty
  obtain ⟨s, hs⟩ := exists_avoid_finite_real (badTriples ∪ badPairs) (hbadT_fin.union hbadP_fin)
  have hsT : s ∉ badTriples := fun h => hs (Or.inl h)
  have hsP : s ∉ badPairs := fun h => hs (Or.inr h)
  let T₁ : (ℝ^3) ≃ₗ[ℝ] (ℝ^3) :=
    { toFun := fun x => !₂[x 1 - s * x 0, x 2 - s ^ 2 * x 0, x 0]
      invFun := fun y => !₂[y 2, y 0 + s * y 2, y 1 + s ^ 2 * y 2]
      left_inv := fun x => by ext k; fin_cases k <;> simp <;> ring
      right_inv := fun y => by ext k; fin_cases k <;> simp <;> ring
      map_add' := fun x y => by ext k; fin_cases k <;> simp <;> ring
      map_smul' := fun r x => by ext k; fin_cases k <;> simp <;> ring }
  let X₁ := X.image T₁
  have hinj1 : Set.InjOn projXY (X₁ : Set (ℝ^3)) := by
    intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy₁
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy₂
    by_contra hne
    have hab : a ≠ b := fun h => hne (by subst h; rfl)
    have h0 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq) 0
    have h1 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq) 1
    simp only [projXY, T₁, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    apply hsP
    refine Set.mem_iUnion₂.mpr ⟨a, ha, Set.mem_iUnion₂.mpr ⟨b, hb, ?_⟩⟩
    rw [if_pos hab]
    exact ⟨by linarith, by linarith⟩
  have hgp1 : IsGP2 (X₁.image projXY) := by
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ h12 h23 h13
    obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hp₁
    obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hp₂
    obtain ⟨y₃, hy₃, rfl⟩ := Finset.mem_image.mp hp₃
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy₁
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy₂
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy₃
    have hab : a ≠ b := fun h => h12 (by subst h; rfl)
    have hbc : b ≠ c := fun h => h23 (by subst h; rfl)
    have hac : a ≠ c := fun h => h13 (by subst h; rfl)
    intro hor0
    apply hsT
    refine Set.mem_iUnion₂.mpr ⟨a, ha, Set.mem_iUnion₂.mpr ⟨b, hb, Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩⟩⟩
    rw [if_pos ⟨hab, hbc, hac⟩]
    simp only [Set.mem_setOf_eq, cross3, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val]
    simp only [orient2, projXY, T₁, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hor0
    linarith
  -- Step 2: shear x₀ ↦ x₀ + τ * x₁ to make all x₀-coordinates distinct!
  let badShear : Set ℝ :=
    ⋃ y₁ ∈ X₁, ⋃ y₂ ∈ X₁,
      if y₁ ≠ y₂ ∧ y₂ 1 - y₁ 1 ≠ 0 then {-(y₂ 0 - y₁ 0) / (y₂ 1 - y₁ 1)} else ∅
  have hbadS_fin : badShear.Finite := by
    refine X₁.finite_toSet.biUnion fun y₁ _ => X₁.finite_toSet.biUnion fun y₂ _ => ?_
    split_ifs
    · exact Set.finite_singleton _
    · exact Set.finite_empty
  obtain ⟨τ, hτ⟩ := exists_avoid_finite_real badShear hbadS_fin
  let T₂ : (ℝ^3) ≃ₗ[ℝ] (ℝ^3) :=
    { toFun := fun y => !₂[y 0 + τ * y 1, y 1, y 2]
      invFun := fun z => !₂[z 0 - τ * z 1, z 1, z 2]
      left_inv := fun y => by ext k; fin_cases k <;> simp <;> ring
      right_inv := fun z => by ext k; fin_cases k <;> simp <;> ring
      map_add' := fun u v => by ext k; fin_cases k <;> simp <;> ring
      map_smul' := fun r u => by ext k; fin_cases k <;> simp <;> ring }
  refine ⟨T₁.trans T₂, ?_, ?_, ?_⟩
  · -- InjOn projXY on X.image (T₁.trans T₂)
    intro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz₂
    have h0 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq) 0
    have h1 := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) heq) 1
    simp only [projXY, LinearEquiv.trans_apply, T₂, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    have hproj_eq : projXY (T₁ a) = projXY (T₁ b) := by
      ext k; fin_cases k
      · have : τ * (T₁ a) 1 = τ * (T₁ b) 1 := by rw [h1]
        simp [projXY]; linarith
      · simp [projXY]; exact h1
    have hT1eq := hinj1 (Finset.mem_image_of_mem T₁ ha) (Finset.mem_image_of_mem T₁ hb) hproj_eq
    simp only [LinearEquiv.trans_apply, hT1eq]
  · -- IsGP2
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ h12 h23 h13
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hp₁
    obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.mp hp₂
    obtain ⟨z₃, hz₃, rfl⟩ := Finset.mem_image.mp hp₃
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz₂
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz₃
    have hor_eq : orient2 (projXY (T₂ (T₁ a))) (projXY (T₂ (T₁ b))) (projXY (T₂ (T₁ c))) =
        orient2 (projXY (T₁ a)) (projXY (T₁ b)) (projXY (T₁ c)) := by
      simp only [orient2, projXY, T₂, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    simp only [LinearEquiv.trans_apply, hor_eq]
    exact hgp1 _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ ha))
      _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hb))
      _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hc))
      (fun h => h12 (by
        have hT1 := hinj1 (Finset.mem_image_of_mem T₁ ha) (Finset.mem_image_of_mem T₁ hb) h
        simp [LinearEquiv.trans_apply, hT1]))
      (fun h => h23 (by
        have hT1 := hinj1 (Finset.mem_image_of_mem T₁ hb) (Finset.mem_image_of_mem T₁ hc) h
        simp [LinearEquiv.trans_apply, hT1]))
      (fun h => h13 (by
        have hT1 := hinj1 (Finset.mem_image_of_mem T₁ ha) (Finset.mem_image_of_mem T₁ hc) h
        simp [LinearEquiv.trans_apply, hT1]))
  · -- DistinctX2
    intro p₁ hp₁ p₂ hp₂ hne heq
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hp₁
    obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.mp hp₂
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz₂
    have hy1 : T₁ a ∈ X₁ := Finset.mem_image_of_mem T₁ ha
    have hy2 : T₁ b ∈ X₁ := Finset.mem_image_of_mem T₁ hb
    have hyne : T₁ a ≠ T₁ b := fun h => hne (by simp [LinearEquiv.trans_apply, h])
    simp only [projXY, LinearEquiv.trans_apply, T₂, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_zero] at heq
    by_cases h1 : T₁ b 1 - T₁ a 1 = 0
    · have hτe : τ * (T₁ a) 1 = τ * (T₁ b) 1 := by rw [show (T₁ b) 1 = (T₁ a) 1 by linarith]
      have h0 : T₁ b 0 = T₁ a 0 := by linarith
      have hproj : projXY (T₁ a) = projXY (T₁ b) := by
        ext k; fin_cases k
        · simp [projXY, h0]
        · simp [projXY]; linarith
      exact hyne (hinj1 hy1 hy2 hproj)
    · apply hτ
      refine Set.mem_iUnion₂.mpr ⟨T₁ a, hy1, Set.mem_iUnion₂.mpr ⟨T₁ b, hy2, ?_⟩⟩
      rw [if_pos ⟨hyne, h1⟩, Set.mem_singleton_iff]
      exact eq_div_of_mul_eq h1 (by linarith)

/-! ## Section 7: 2-Separability via Centerpoints -/

def Is2Separated (k : ℕ) (Xs : Fin k → Finset (ℝ^3)) : Prop :=
  ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
    Disjoint (convexHull ℝ ((Xs i ∪ Xs j : Finset (ℝ^3)) : Set (ℝ^3)))
             (convexHull ℝ ((Xs i' ∪ Xs j' : Finset (ℝ^3)) : Set (ℝ^3)))

lemma gp3_at_most_three_on_plane {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X)
    (f : (ℝ^3) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    (X.filter (fun x => f x = c)).card ≤ 3 := by
  classical
  by_contra hgt
  push_neg at hgt
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ (X.filter (fun x => f x = c)).card by omega)
  have hYX : Y ⊆ X := hYsub.trans (Finset.filter_subset _ _)
  have hind := hX Y hYX (by omega)
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y₀, hy₀⟩ := hYne
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥(Y : Set (ℝ^3)) → ℝ^3)
    ⟨y₀, hy₀⟩).mp hind
  -- All `y - y₀` (`y ∈ Y \ {y₀}`) lie in `LinearMap.ker f`, which has finrank 2!
  have hsub_ker : ∀ i : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨y₀, hy₀⟩},
      i.val.val -ᵥ y₀ ∈ LinearMap.ker f := by
    intro i
    rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
    have h1 := (Finset.mem_filter.mp (hYsub i.val.prop)).2
    have h2 := (Finset.mem_filter.mp (hYsub hy₀)).2
    linarith
  let g : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨y₀, hy₀⟩} → LinearMap.ker f :=
    fun i => ⟨i.val.val -ᵥ y₀, hsub_ker i⟩
  have hlin_ker : LinearIndependent ℝ g :=
    LinearIndependent.of_comp (LinearMap.ker f).subtype hlin
  have hcard_le : Fintype.card {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨y₀, hy₀⟩} ≤
      Module.finrank ℝ (LinearMap.ker f) := hlin_ker.fintype_card_le_finrank
  have hcard_eq : Fintype.card {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨y₀, hy₀⟩} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; simp [hYcard]
  have hker_dim : Module.finrank ℝ (LinearMap.ker f) = 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    rw [finrank_euclideanSpace_fin] at hrk
    have hrange_pos : 1 ≤ Module.finrank ℝ (LinearMap.range f) := by
      have hne_bot : LinearMap.range f ≠ ⊥ := by
        intro hbot; apply hf; ext x
        have : f x ∈ (⊥ : Submodule ℝ ℝ) := hbot ▸ LinearMap.mem_range_self f x
        exact this
      exact Nat.pos_of_ne_zero (fun h0 => hne_bot (Submodule.finrank_eq_zero.mp h0))
    omega
  omega

lemma separate_four_sets {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X)
    {A₁ A₂ A₃ A₄ : Finset (ℝ^3)}
    (h1 : A₁ ⊆ X) (h2 : A₂ ⊆ X) (h3 : A₃ ⊆ X) (h4 : A₄ ⊆ X)
    (hc1 : 24 ≤ A₁.card) (hc2 : 24 ≤ A₂.card) (hc3 : 24 ≤ A₃.card) (hc4 : 24 ≤ A₄.card) :
    ∃ B₁ B₂ B₃ B₄ : Finset (ℝ^3),
      B₁ ⊆ A₁ ∧ B₂ ⊆ A₂ ∧ B₃ ⊆ A₃ ∧ B₄ ⊆ A₄ ∧
      A₁.card ≤ 8 * B₁.card ∧ A₂.card ≤ 8 * B₂.card ∧
      A₃.card ≤ 8 * B₃.card ∧ A₄.card ≤ 8 * B₄.card ∧
      Disjoint (convexHull ℝ ((B₁ ∪ B₂ : Finset (ℝ^3)) : Set (ℝ^3)))
               (convexHull ℝ ((B₃ ∪ B₄ : Finset (ℝ^3)) : Set (ℝ^3))) := by
  classical
  obtain ⟨p₁, hp₁⟩ := centerpoint_theorem A₁ (Finset.card_pos.mp (by omega))
  obtain ⟨p₂, hp₂⟩ := centerpoint_theorem A₂ (Finset.card_pos.mp (by omega))
  obtain ⟨p₃, hp₃⟩ := centerpoint_theorem A₃ (Finset.card_pos.mp (by omega))
  obtain ⟨p₄, hp₄⟩ := centerpoint_theorem A₄ (Finset.card_pos.mp (by omega))
  -- Find nonzero linear functional `f : ℝ^3 →ₗ[ℝ] ℝ` vanishing on `p₂ - p₁` and `p₃ - p₁`.
  let ev : (ℝ^3) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun v =>
        (v 0 * (p₂ 0 - p₁ 0) + v 1 * (p₂ 1 - p₁ 1) + v 2 * (p₂ 2 - p₁ 2),
         v 0 * (p₃ 0 - p₁ 0) + v 1 * (p₃ 1 - p₁ 1) + v 2 * (p₃ 2 - p₁ 2))
      map_add' := fun u w => by ext <;> simp <;> ring
      map_smul' := fun r u => by ext <;> simp <;> ring }
  have hnotinj : ¬ Function.Injective ev := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [finrank_euclideanSpace_fin, Module.finrank_prod, Module.finrank_self] at hle
    omega
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnotinj
  push_neg at hnotinj
  obtain ⟨v₀, hv₀ker, hv₀ne⟩ := hnotinj
  let f₀ : (ℝ^3) →ₗ[ℝ] ℝ :=
    { toFun := fun x => v₀ 0 * x 0 + v₀ 1 * x 1 + v₀ 2 * x 2
      map_add' := fun x y => by simp; ring
      map_smul' := fun r x => by simp; ring }
  have hf₀_ne : f₀ ≠ 0 := by
    intro h0; apply hv₀ne; ext k
    have := congrArg (fun g : (ℝ^3) →ₗ[ℝ] ℝ => g (EuclideanSpace.single k (1 : ℝ))) h0
    fin_cases k <;> simpa [f₀, EuclideanSpace.single_apply] using this
  have hker_eq := LinearMap.mem_ker.mp hv₀ker
  have hf₀12 : f₀ p₂ = f₀ p₁ := by
    have := congrArg Prod.fst hker_eq; simp only [ev, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_zero] at this
    simp only [f₀, LinearMap.coe_mk, AddHom.coe_mk]; linarith
  have hf₀13 : f₀ p₃ = f₀ p₁ := by
    have := congrArg Prod.snd hker_eq; simp only [ev, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_zero] at this
    simp only [f₀, LinearMap.coe_mk, AddHom.coe_mk]; linarith
  -- Orient `f` so `f p₄ ≤ f p₁`!
  let sgn : ℝ := if f₀ p₄ ≤ f₀ p₁ then 1 else -1
  let f : (ℝ^3) →ₗ[ℝ] ℝ := sgn • f₀
  let c : ℝ := f p₁
  have hf_ne : f ≠ 0 := by
    intro h0; apply hf₀_ne
    have hsgn : sgn ≠ 0 := by dsimp only [sgn]; split_ifs <;> norm_num
    exact (smul_eq_zero.mp h0).resolve_left hsgn
  have hfp1 : c ≤ f p₁ := le_rfl
  have hfp2 : c ≤ f p₂ := by simp only [c, f, LinearMap.smul_apply, hf₀12, le_rfl]
  have hfp3 : f p₃ ≤ c := by simp only [c, f, LinearMap.smul_apply, hf₀13, le_rfl]
  have hfp4 : f p₄ ≤ c := by
    simp only [c, f, LinearMap.smul_apply, smul_eq_mul, sgn]
    split_ifs with hle <;> linarith
  let B₁ := A₁.filter (fun x => c < f x)
  let B₂ := A₂.filter (fun x => c < f x)
  let B₃ := A₃.filter (fun x => f x < c)
  let B₄ := A₄.filter (fun x => f x < c)
  have hgt_bound : ∀ A : Finset (ℝ^3), A ⊆ X → 24 ≤ A.card →
      A.card ≤ 4 * (A.filter fun x => c ≤ f x).card →
      A.card ≤ 8 * (A.filter fun x => c < f x).card := by
    intro A hAX hAcard hcp
    have heq_le : (A.filter fun x => f x = c).card ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hAX)).trans
        (gp3_at_most_three_on_plane hX f hf_ne c)
    have hsub : A.filter (fun x => c ≤ f x) ⊆
        A.filter (fun x => c < f x) ∪ A.filter (fun x => f x = c) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      rcases lt_or_eq_of_le hx'.2 with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx'.1, heq.symm⟩)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hlt_bound : ∀ A : Finset (ℝ^3), A ⊆ X → 24 ≤ A.card →
      A.card ≤ 4 * (A.filter fun x => -c ≤ (-f) x).card →
      A.card ≤ 8 * (A.filter fun x => f x < c).card := by
    intro A hAX hAcard hcp
    have heq_le : (A.filter fun x => f x = c).card ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hAX)).trans
        (gp3_at_most_three_on_plane hX f hf_ne c)
    have hsub : A.filter (fun x => -c ≤ (-f) x) ⊆
        A.filter (fun x => f x < c) ∪ A.filter (fun x => f x = c) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      simp only [LinearMap.neg_apply, neg_le_neg_iff] at hx'
      rcases lt_or_eq_of_le hx'.2 with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx'.1, heq⟩)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  refine ⟨B₁, B₂, B₃, B₄, Finset.filter_subset _ _, Finset.filter_subset _ _,
    Finset.filter_subset _ _, Finset.filter_subset _ _,
    hgt_bound A₁ h1 hc1 (hp₁ f c hfp1),
    hgt_bound A₂ h2 hc2 (hp₂ f c hfp2),
    hlt_bound A₃ h3 hc3 (hp₃ (-f) (-c) (by simp [hfp3])),
    hlt_bound A₄ h4 hc4 (hp₄ (-f) (-c) (by simp [hfp4])), ?_⟩
  rw [Set.disjoint_left]
  intro p hp1 hp2
  have hconv1 : Convex ℝ {x : ℝ^3 | c < f x} := convex_halfSpace_gt f.isLinear c
  have hconv2 : Convex ℝ {x : ℝ^3 | f x < c} := convex_halfSpace_lt f.isLinear c
  have h1gt : c < f p := hconv1.convexHull_subset_iff.mpr (by
    intro x hx; rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx1 | hx2
    · exact (Finset.mem_filter.mp hx1).2
    · exact (Finset.mem_filter.mp hx2).2) hp1
  have h2lt : f p < c := hconv2.convexHull_subset_iff.mpr (by
    intro x hx; rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx3 | hx4
    · exact (Finset.mem_filter.mp hx3).2
    · exact (Finset.mem_filter.mp hx4).2) hp2
  linarith

lemma two_separated_clusters {k : ℕ} {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X)
    (Xs : Fin k → Finset (ℝ^3))
    (hXs_sub : ∀ i, Xs i ⊆ X)
    (hXs_sep : ∀ i : Fin k, ∃ (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ),
      (∀ x ∈ Xs i, φ x < c) ∧ (∀ j : Fin k, j ≠ i → ∀ x ∈ Xs j, c < φ x))
    (M : ℕ) (hXs_big : ∀ i, 24 * 8 ^ (k ^ 4) ≤ (Xs i).card) :
    ∃ Ys : Fin k → Finset (ℝ^3),
      (∀ i, Ys i ⊆ Xs i) ∧
      (∀ i, (Xs i).card ≤ 8 ^ (k ^ 4) * (Ys i).card) ∧
      Is2Separated k Ys := by
  classical
  -- List all 4-tuples `(i, j, i', j')` of pairwise distinct indices in `Fin k`.
  let allQuads : List (Fin k × Fin k × Fin k × Fin k) :=
    ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin k)).filter (fun q =>
      q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
      q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2)).toList
  have hlen_le : allQuads.length ≤ k ^ 4 := by
    rw [Finset.length_toList]
    calc ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin k)).filter _).card
        ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin k)).card :=
          Finset.card_filter_le _ _
      _ = k ^ 4 := by simp [pow_succ]; ring
  -- Induct on prefixes of `allQuads`!
  have hstep : ∀ (L : List (Fin k × Fin k × Fin k × Fin k)),
      L.length ≤ k ^ 4 →
      (∀ q ∈ L, q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
        q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2) →
      ∃ Ys : Fin k → Finset (ℝ^3),
        (∀ i, Ys i ⊆ Xs i) ∧
        (∀ i, (Xs i).card ≤ 8 ^ L.length * (Ys i).card) ∧
        (∀ q ∈ L, Disjoint (convexHull ℝ ((Ys q.1 ∪ Ys q.2.1 : Finset (ℝ^3)) : Set (ℝ^3)))
                           (convexHull ℝ ((Ys q.2.2.1 ∪ Ys q.2.2.2 : Finset (ℝ^3)) : Set (ℝ^3)))) := by
    intro L
    induction L with
    | nil =>
      intro _ _
      exact ⟨Xs, fun _ => (Finset.Subset.refl _), fun _ => by simp, by simp⟩
    | cons q rest ih =>
      intro hLlen hLdist
      have hq := hLdist q List.mem_cons_self
      obtain ⟨Zs, hZs_sub, hZs_card, hZs_disj⟩ :=
        ih (by simp at hLlen; omega) (fun r hr => hLdist r (List.mem_cons_of_mem _ hr))
      have hZbig : ∀ i, 24 ≤ (Zs i).card := fun i => by
        have h1 := hXs_big i
        have h2 := hZs_card i
        have hpow : 8 ^ rest.length ≤ 8 ^ (k ^ 4) := Nat.pow_le_pow_right (by omega) (by simp at hLlen; omega)
        have h3 : 24 * 8 ^ rest.length ≤ 8 ^ rest.length * (Zs i).card :=
          (Nat.mul_le_mul_left 24 hpow).trans (h1.trans h2)
        have hpos : 0 < 8 ^ rest.length := pow_pos (by omega) _
        nlinarith
      obtain ⟨B₁, B₂, B₃, B₄, hB₁, hB₂, hB₃, hB₄, hc₁, hc₂, hc₃, hc₄, hdisj⟩ :=
        separate_four_sets hX
          ((hZs_sub q.1).trans (hXs_sub q.1))
          ((hZs_sub q.2.1).trans (hXs_sub q.2.1))
          ((hZs_sub q.2.2.1).trans (hXs_sub q.2.2.1))
          ((hZs_sub q.2.2.2).trans (hXs_sub q.2.2.2))
          (hZbig q.1) (hZbig q.2.1) (hZbig q.2.2.1) (hZbig q.2.2.2)
      let Ys : Fin k → Finset (ℝ^3) := fun i =>
        if i = q.1 then B₁
        else if i = q.2.1 then B₂
        else if i = q.2.2.1 then B₃
        else if i = q.2.2.2 then B₄
        else Zs i
      have hYs_sub_Zs : ∀ i, Ys i ⊆ Zs i := fun i => by
        dsimp only [Ys]; split_ifs with h1 h2 h3 h4
        · subst h1; exact hB₁
        · subst h2; exact hB₂
        · subst h3; exact hB₃
        · subst h4; exact hB₄
        · exact (Finset.Subset.refl _)
      have hYs_card : ∀ i, (Zs i).card ≤ 8 * (Ys i).card := fun i => by
        dsimp only [Ys]; split_ifs with h1 h2 h3 h4
        · subst h1; exact hc₁
        · subst h2; exact hc₂
        · subst h3; exact hc₃
        · subst h4; exact hc₄
        · omega
      refine ⟨Ys, fun i => (hYs_sub_Zs i).trans (hZs_sub i), fun i => ?_, fun r hr => ?_⟩
      · simp only [List.length_cons, pow_succ]
        calc (Xs i).card ≤ 8 ^ rest.length * (Zs i).card := hZs_card i
          _ ≤ 8 ^ rest.length * (8 * (Ys i).card) := Nat.mul_le_mul_left _ (hYs_card i)
          _ = 8 ^ rest.length * 8 * (Ys i).card := by ring
      · rcases List.mem_cons.mp hr with hrq | hrest
        · rw [hrq]
          have h1 : Ys q.1 = B₁ := by simp [Ys]
          have h2 : Ys q.2.1 = B₂ := by simp [Ys, hq.1.symm]
          have h3 : Ys q.2.2.1 = B₃ := by simp [Ys, hq.2.1.symm, hq.2.2.2.1.symm]
          have h4 : Ys q.2.2.2 = B₄ := by simp [Ys, hq.2.2.1.symm, hq.2.2.2.2.1.symm, hq.2.2.2.2.2.symm]
          rwa [h1, h2, h3, h4]
        · exact (hZs_disj r hrest).mono
            (convexHull_mono (Finset.coe_subset.mpr (Finset.union_subset_union (hYs_sub_Zs _) (hYs_sub_Zs _))))
            (convexHull_mono (Finset.coe_subset.mpr (Finset.union_subset_union (hYs_sub_Zs _) (hYs_sub_Zs _))))
  obtain ⟨Ys, hYs_sub, hYs_card, hYs_disj⟩ := hstep allQuads hlen_le (fun q hq => by
    have := (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).2; exact this)
  refine ⟨Ys, hYs_sub, fun i => (hYs_card i).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hlen_le)), ?_⟩
  intro i j i' j' h1 h2 h3 h4
  by_cases hij : i = j
  · subst hij
    obtain ⟨φ, c, hlt, hgt⟩ := hXs_sep i
    rw [Finset.union_idempotent, Set.disjoint_left]
    intro p hp1 hp2
    have hlt_p : φ p < c := (convex_halfSpace_lt φ.isLinear c).convexHull_subset_iff.mpr
      (fun x hx => hlt x (hYs_sub i hx)) hp1
    have hgt_p : c < φ p := (convex_halfSpace_gt φ.isLinear c).convexHull_subset_iff.mpr
      (fun x hx => by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx1 | hx2
        · exact hgt i' h1.symm x (hYs_sub i' hx1)
        · exact hgt j' h2.symm x (hYs_sub j' hx2)) hp2
    linarith
  · by_cases hi'j' : i' = j'
    · subst hi'j'
      obtain ⟨φ, c, hlt, hgt⟩ := hXs_sep i'
      rw [Finset.union_idempotent, Set.disjoint_left]
      intro p hp1 hp2
      have hgt_p : c < φ p := (convex_halfSpace_gt φ.isLinear c).convexHull_subset_iff.mpr
        (fun x hx => by
          rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx1 | hx2
          · exact hgt i h1 x (hYs_sub i hx1)
          · exact hgt j h3 x (hYs_sub j hx2)) hp1
      have hlt_p : φ p < c := (convex_halfSpace_lt φ.isLinear c).convexHull_subset_iff.mpr
        (fun x hx => hlt x (hYs_sub i' hx)) hp2
      linarith
    · exact hYs_disj (i, j, i', j') (Finset.mem_toList.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hij, h1, h2, h3, h4, hi'j'⟩))

/-! ## Section 8: Above/Below (Props 2.4, 2.5, Cor 2.6) & Tubular Separation (Prop 2.9) -/

/-- For four points `a, c, b, d ∈ ℝ^3` whose projections are in strict CCW order `(a, c, b, d)`,
`segAbove a b c d` means the segment `ab` passes strictly above `cd` at their projected intersection. -/
def segAbove (a b c d : ℝ^3) : Prop :=
  let Δ₁ := orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b)
  let Δ₂ := orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c)
  let lam := orient2 (projXY c) (projXY d) (projXY a) / Δ₁
  let mu := (-orient2 (projXY a) (projXY b) (projXY c)) / Δ₂
  (1 - mu) * c 2 + mu * d 2 < (1 - lam) * a 2 + lam * b 2

lemma seg_proj_intersection {a b c d : ℝ^3}
    (h1 : 0 < orient2 (projXY a) (projXY c) (projXY b))
    (h2 : 0 < orient2 (projXY a) (projXY b) (projXY d))
    (h3 : 0 < orient2 (projXY c) (projXY b) (projXY d))
    (h4 : 0 < orient2 (projXY a) (projXY c) (projXY d)) :
    let Δ₁ := orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b)
    let Δ₂ := orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c)
    let lam := orient2 (projXY c) (projXY d) (projXY a) / Δ₁
    let mu := (-orient2 (projXY a) (projXY b) (projXY c)) / Δ₂
    0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧
      (1 - lam) • projXY a + lam • projXY b = (1 - mu) • projXY c + mu • projXY d := by
  have e1 : orient2 (projXY c) (projXY d) (projXY a) = orient2 (projXY a) (projXY c) (projXY d) := by
    unfold orient2; ring
  have e2 : orient2 (projXY c) (projXY d) (projXY b) = - orient2 (projXY c) (projXY b) (projXY d) := by
    unfold orient2; ring
  have e3 : orient2 (projXY a) (projXY b) (projXY c) = - orient2 (projXY a) (projXY c) (projXY b) := by
    unfold orient2; ring
  have hcda : 0 < orient2 (projXY c) (projXY d) (projXY a) := by rw [e1]; exact h4
  have hcdb : orient2 (projXY c) (projXY d) (projXY b) < 0 := by rw [e2]; linarith
  have habc : orient2 (projXY a) (projXY b) (projXY c) < 0 := by rw [e3]; linarith
  have hΔ₁ : 0 < orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) := by
    linarith
  have hΔ₂ : 0 < orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) := by
    linarith
  have hΔeq : orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) =
      orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) := by
    unfold orient2; ring
  refine ⟨div_pos hcda hΔ₁, (div_lt_one hΔ₁).mpr (by linarith),
    div_pos (by linarith) hΔ₂, (div_lt_one hΔ₂).mpr (by linarith), ?_⟩
  ext k; fin_cases k <;>
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← hΔeq]
    field_simp [hΔ₁.ne']
    unfold orient2; simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring

lemma segAbove_or_below {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X)
    {a c b d : ℝ^3} (ha : a ∈ X) (hc : c ∈ X) (hb : b ∈ X) (hd : d ∈ X)
    (h1 : 0 < orient2 (projXY a) (projXY c) (projXY b))
    (h2 : 0 < orient2 (projXY a) (projXY b) (projXY d))
    (h3 : 0 < orient2 (projXY c) (projXY b) (projXY d))
    (h4 : 0 < orient2 (projXY a) (projXY c) (projXY d)) :
    segAbove a b c d ∨ segAbove c d a b := by
  classical
  have hmem := seg_proj_intersection h1 h2 h3 h4
  obtain ⟨hlam0, hlam1, hmu0, hmu1, hpeq⟩ := hmem
  -- Check that `a, c, b, d` are all pairwise distinct!
  have hac : a ≠ c := fun h => by subst h; rw [orient2_self_left] at h1; linarith
  have hab : a ≠ b := fun h => by subst h; rw [orient2_self_outer] at h1; linarith
  have had : a ≠ d := fun h => by subst h; rw [orient2_self_outer] at h2; linarith
  have hcb : c ≠ b := fun h => by subst h; rw [orient2_self_right] at h1; linarith
  have hcd : c ≠ d := fun h => by subst h; rw [orient2_self_right] at h4; linarith
  have hbd : b ≠ d := fun h => by subst h; rw [orient2_self_right] at h2; linarith
  let Δ₁ := orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b)
  let Δ₂ := orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c)
  let lam := orient2 (projXY c) (projXY d) (projXY a) / Δ₁
  let mu := (-orient2 (projXY a) (projXY b) (projXY c)) / Δ₂
  have hneq : (1 - mu) * c 2 + mu * d 2 ≠ (1 - lam) * a 2 + lam * b 2 := by
    intro heq3
    -- Then `(1 - lam) • a + lam • b = (1 - mu) • c + mu • d`, contradicting `AffineIndependent` of `{a, b, c, d}`!
    have hveq : (1 - lam) • a + lam • b = (1 - mu) • c + mu • d := by
      ext k; fin_cases k
      · exact congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) hpeq) 0
      · exact congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) hpeq) 1
      · exact heq3.symm
    let Y : Finset (ℝ^3) := {a, b, c, d}
    have hYX : Y ⊆ X := by
      intro x hx; simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hYcard : Y.card ≤ 4 := by
      calc Y.card ≤ ({b, c, d} : Finset (ℝ^3)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({c, d} : Finset (ℝ^3)).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ ≤ 2 + 1 + 1 := Nat.add_le_add_right (Nat.add_le_add_right Finset.card_le_two 1) 1
    have hind := hX Y hYX hYcard
    have haY : a ∈ Y := by simp [Y]
    have hbY : b ∈ Y := by simp [Y]
    have hcY : c ∈ Y := by simp [Y]
    have hdY : d ∈ Y := by simp [Y]
    have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥(Y : Set (ℝ^3)) → ℝ^3)
      ⟨a, haY⟩).mp hind
    let ib : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} := ⟨⟨b, hbY⟩, fun h => hab (congrArg Subtype.val h).symm⟩
    let ic : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} := ⟨⟨c, hcY⟩, fun h => hac (congrArg Subtype.val h).symm⟩
    let id_ : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} := ⟨⟨d, hdY⟩, fun h => had (congrArg Subtype.val h).symm⟩
    have hibc : ib ≠ ic := fun h => hcb (congrArg (fun z => z.val.val) h).symm
    have hibd : ib ≠ id_ := fun h => hbd (congrArg (fun z => z.val.val) h)
    have hicd : ic ≠ id_ := fun h => hcd (congrArg (fun z => z.val.val) h)
    have hcomb : lam • (b -ᵥ a) + (-(1 - mu)) • (c -ᵥ a) + (-mu) • (d -ᵥ a) = 0 := by
      ext k
      have hk := congrFun (congrArg (fun v : ℝ^3 => (v : Fin 3 → ℝ)) hveq) k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply,
        PiLp.zero_apply] at hk ⊢
      linarith
    let coef : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩} → ℝ := fun i =>
      if i = ib then lam else if i = ic then -(1 - mu) else if i = id_ then -mu else 0
    have hsum0 : ∑ i, coef i • (i.val.val -ᵥ a) = 0 := by
      have huniv : (Finset.univ : Finset {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨a, haY⟩}) = {ib, ic, id_} := by
        ext i; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        have hiY : i.val.val ∈ Y := Finset.mem_coe.mp i.val.prop
        simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hiY
        rcases hiY with h | h | h | h
        · exact (i.prop (Subtype.ext h)).elim
        · left; exact Subtype.ext (Subtype.ext h)
        · right; left; exact Subtype.ext (Subtype.ext h)
        · right; right; exact Subtype.ext (Subtype.ext h)
      rw [huniv, Finset.sum_insert (by simp [hibc, hibd]), Finset.sum_insert (by simp [hicd]),
          Finset.sum_singleton]
      simp only [coef, ite_true, hibc.symm, hibd.symm, hicd.symm, ite_false]
      rw [← add_assoc]; exact hcomb
    have hlam_eq0 := Fintype.linearIndependent_iff.mp hlin coef hsum0 ib
    simp only [coef, ite_true] at hlam_eq0
    linarith
  -- Check `segAbove c d a b` equals `(1 - lam) * a 2 + lam * b 2 < (1 - mu) * c 2 + mu * d 2`!
  have hsym : segAbove c d a b ↔ (1 - lam) * a 2 + lam * b 2 < (1 - mu) * c 2 + mu * d 2 := by
    unfold segAbove
    have h1' : orient2 (projXY a) (projXY b) (projXY c) - orient2 (projXY a) (projXY b) (projXY d) = -Δ₂ := by
      dsimp only [Δ₂]; ring
    have h2' : orient2 (projXY c) (projXY d) (projXY b) - orient2 (projXY c) (projXY d) (projXY a) = -Δ₁ := by
      dsimp only [Δ₁]; ring
    have hlam' : (-orient2 (projXY c) (projXY d) (projXY a)) / (-Δ₁) = lam := by
      dsimp only [lam]; rw [neg_div_neg_eq]
    have hmu' : orient2 (projXY a) (projXY b) (projXY c) / (-Δ₂) = mu := by
      dsimp only [mu]; rw [div_neg, ← neg_div]
    simp only [h1', h2', hmu']
    rw [show (-orient2 (projXY c) (projXY d) (projXY a)) / (-Δ₁) = lam from hlam']
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr (hsym.mpr hgt)

/-! ## Section 9: signed volumes and above/below -/

/-- Signed volume `det (b - a, c - a, d - a)`. -/
def vol (a b c d : ℝ^3) : ℝ :=
  (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1))
  - (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0))
  + (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0))

/-- The four projected orientation conditions of `segAbove_or_below`: `(a, c, b, d)` is a strictly
convex counterclockwise quadrilateral in projection. -/
def CCW4 (a c b d : ℝ^3) : Prop :=
  0 < orient2 (projXY a) (projXY c) (projXY b) ∧
  0 < orient2 (projXY a) (projXY b) (projXY d) ∧
  0 < orient2 (projXY c) (projXY b) (projXY d) ∧
  0 < orient2 (projXY a) (projXY c) (projXY d)

lemma projXY_apply0 (x : ℝ^3) : projXY x 0 = x 0 := by simp [projXY]
lemma projXY_apply1 (x : ℝ^3) : projXY x 1 = x 1 := by simp [projXY]

lemma orient2_projXY (a b c : ℝ^3) :
    orient2 (projXY a) (projXY b) (projXY c) =
      (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) := by
  simp [orient2, projXY_apply0, projXY_apply1]

lemma CCW4_rot {a c b d : ℝ^3} (h : CCW4 a c b d) : CCW4 c b d a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [CCW4, orient2_projXY] at *
  refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma vol_identity (a b c d : ℝ^3)
    (hΔ : orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) ≠ 0)
    (hΔ' : orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) ≠ 0) :
    vol a b c d =
      (orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b)) *
      (((1 - orient2 (projXY c) (projXY d) (projXY a) /
          (orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b))) * a 2
        + orient2 (projXY c) (projXY d) (projXY a) /
          (orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b)) * b 2)
      - ((1 - (-orient2 (projXY a) (projXY b) (projXY c)) /
          (orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c))) * c 2
        + (-orient2 (projXY a) (projXY b) (projXY c)) /
          (orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c)) * d 2)) := by
  have hE : orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) =
      orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) := by
    simp only [orient2_projXY]; ring
  rw [hE]
  rw [hE] at hΔ'
  field_simp
  simp only [vol, orient2_projXY]
  ring

lemma CCW4_delta_pos {a c b d : ℝ^3} (h : CCW4 a c b d) :
    0 < orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [orient2_projXY] at *
  nlinarith

lemma segAbove_iff_vol {a c b d : ℝ^3} (h : CCW4 a c b d) :
    segAbove a b c d ↔ 0 < vol a b c d := by
  have hΔ := CCW4_delta_pos h
  have hE : orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) =
      orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) := by
    simp only [orient2_projXY]; ring
  rw [vol_identity a b c d hΔ.ne' (by rw [hE]; exact hΔ.ne')]
  unfold segAbove
  simp only
  constructor
  · intro hlt; exact mul_pos hΔ (by linarith)
  · intro hpos
    have := (pos_iff_pos_of_mul_pos hpos).mp hΔ
    linarith

/-- If the two segments are disjoint, the four points are not coplanar. -/
lemma vol_ne_zero {a c b d : ℝ^3} (h : CCW4 a c b d)
    (hdisj : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      (1 - s) • a + s • b ≠ (1 - t) • c + t • d) :
    vol a b c d ≠ 0 := by
  intro hv
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨hl0, hl1, hm0, hm1, hpeq⟩ := seg_proj_intersection h1 h2 h3 h4
  have hΔ := CCW4_delta_pos ⟨h1, h2, h3, h4⟩
  have hE : orient2 (projXY a) (projXY b) (projXY d) - orient2 (projXY a) (projXY b) (projXY c) =
      orient2 (projXY c) (projXY d) (projXY a) - orient2 (projXY c) (projXY d) (projXY b) := by
    simp only [orient2_projXY]; ring
  rw [vol_identity a b c d hΔ.ne' (by rw [hE]; exact hΔ.ne')] at hv
  rcases mul_eq_zero.mp hv with h0 | h0
  · exact hΔ.ne' h0
  apply hdisj _ _ hl0.le hl1.le hm0.le hm1.le
  ext k
  fin_cases k
  · have := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) hpeq) 0
    simpa [projXY] using this
  · have := congrFun (congrArg (fun v : ℝ^2 => (v : Fin 2 → ℝ)) hpeq) 1
    simpa [projXY] using this
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.reduceFinMk, Fin.isValue]
    linarith

lemma vol_affine_left (a a' b c d : ℝ^3) (s : ℝ) :
    vol ((1 - s) • a + s • a') b c d = (1 - s) * vol a b c d + s * vol a' b c d := by
  simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma orient2_affine_left (a a' b c : ℝ^3) (s : ℝ) :
    orient2 (projXY ((1 - s) • a + s • a')) (projXY b) (projXY c) =
      (1 - s) * orient2 (projXY a) (projXY b) (projXY c) +
        s * orient2 (projXY a') (projXY b) (projXY c) := by
  simp only [orient2_projXY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma CCW4_segment_left {a a' c b d : ℝ^3} (h : CCW4 a c b d) (h' : CCW4 a' c b d)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : CCW4 ((1 - s) • a + s • a') c b d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  have key : ∀ (p q : ℝ), 0 < p → 0 < q → 0 < (1 - s) * p + s * q := by
    intro p q hp hq
    rcases eq_or_lt_of_le hs0 with rfl | hs
    · simpa using hp
    · nlinarith
  refine ⟨?_, ?_, h3, ?_⟩
  · rw [orient2_affine_left]; exact key _ _ h1 h1'
  · rw [orient2_affine_left]; exact key _ _ h2 h2'
  · rw [orient2_affine_left]; exact key _ _ h4 h4'

/-- Moving the first point along a segment: if every intermediate configuration has disjoint
segments, the sign of the volume does not change. -/
lemma vol_pos_iff_of_segment {a a' c b d : ℝ^3} (h : CCW4 a c b d) (h' : CCW4 a' c b d)
    (hdisj : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      (1 - s) • ((1 - r) • a + r • a') + s • b ≠ (1 - t) • c + t • d) :
    0 < vol a b c d ↔ 0 < vol a' b c d := by
  have hne : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → vol ((1 - r) • a + r • a') b c d ≠ 0 := fun r hr0 hr1 =>
    vol_ne_zero (CCW4_segment_left h h' hr0 hr1) (hdisj r hr0 hr1)
  have h0 : vol a b c d ≠ 0 := by simpa using hne 0 le_rfl zero_le_one
  have h1 : vol a' b c d ≠ 0 := by simpa using hne 1 zero_le_one le_rfl
  have key : ∀ p q : ℝ, p - q ≠ 0 → (1 - p / (p - q)) * p + p / (p - q) * q = 0 := by
    intro p q hpq
    have := div_mul_cancel₀ p hpq
    linear_combination (-1 : ℝ) * this
  constructor
  · intro hp
    by_contra hn
    have hn' : vol a' b c d < 0 := lt_of_le_of_ne (not_lt.mp hn) h1
    have hr := hne (vol a b c d / (vol a b c d - vol a' b c d)) (div_nonneg hp.le (by linarith))
      ((div_le_one (by linarith)).mpr (by linarith))
    apply hr
    rw [vol_affine_left]
    exact key _ _ (by linarith)
  · intro hp
    by_contra hn
    have hn' : vol a b c d < 0 := lt_of_le_of_ne (not_lt.mp hn) h0
    have hr := hne (vol a b c d / (vol a b c d - vol a' b c d))
      (div_nonneg_of_nonpos hn'.le (by linarith))
      ((div_le_one_of_neg (by linarith)).mpr (by linarith))
    apply hr
    rw [vol_affine_left]
    exact key _ _ (by linarith)

lemma vol_rot (a b c d : ℝ^3) : vol c d b a = - vol a b c d := by
  simp only [vol]; ring

/-! ## Section 10: affine functionals and convex hulls -/

def IsAffine2 (G : ℝ^3 → ℝ) : Prop :=
  ∀ x y : ℝ^3, ∀ a b : ℝ, a + b = 1 → G (a • x + b • y) = a * G x + b * G y

lemma convexHull_subset_of_affine_le {G : ℝ^3 → ℝ} (hG : IsAffine2 G) {S : Set (ℝ^3)}
    (hS : ∀ x ∈ S, G x ≤ 0) : ∀ x ∈ convexHull ℝ S, G x ≤ 0 := by
  have hconv : Convex ℝ {x : ℝ^3 | G x ≤ 0} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [hG x y a b hab]; nlinarith
  intro x hx
  exact (convexHull_min hS hconv) hx

lemma convexHull_subset_of_affine_pos {G : ℝ^3 → ℝ} (hG : IsAffine2 G) {S : Set (ℝ^3)}
    (hS : ∀ x ∈ S, 0 < G x) : ∀ x ∈ convexHull ℝ S, 0 < G x := by
  have hconv : Convex ℝ {x : ℝ^3 | 0 < G x} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [hG x y a b hab]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp at hab; subst hab; simpa using hy
    · nlinarith
  intro x hx
  exact (convexHull_min hS hconv) hx

/-- Hulls of two sets on opposite sides of an affine functional are disjoint. -/
lemma disjoint_hulls_of_affine {G : ℝ^3 → ℝ} (hG : IsAffine2 G) {S T : Set (ℝ^3)}
    (hS : ∀ x ∈ S, G x ≤ 0) (hT : ∀ x ∈ T, 0 < G x) :
    Disjoint (convexHull ℝ S) (convexHull ℝ T) := by
  rw [Set.disjoint_left]
  intro x hxS hxT
  have h1 := convexHull_subset_of_affine_le hG hS x hxS
  have h2 := convexHull_subset_of_affine_pos hG hT x hxT
  linarith

lemma isAffine2_linear (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ) : IsAffine2 (fun x => φ x - c) := by
  intro x y a b hab
  simp only [map_add, map_smul, smul_eq_mul]
  have : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  linarith

lemma isAffine2_orient (e0 e1 : ℝ^3) :
    IsAffine2 (fun x => orient2 (projXY e0) (projXY e1) (projXY x)) := by
  intro x y a b hab
  simp only [orient2_projXY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb : b = 1 - a := by linarith
  subst hb; ring

lemma isAffine2_vol4 (p q u : ℝ^3) : IsAffine2 (fun y => vol p q u y) := by
  intro x y a b hab
  have hb : b = 1 - a := by linarith
  subst hb; simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma isAffine2_vol3 (p q v : ℝ^3) : IsAffine2 (fun y => vol p q y v) := by
  intro x y a b hab
  have hb : b = 1 - a := by linarith
  subst hb; simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma isAffine2_vol2 (p u v : ℝ^3) : IsAffine2 (fun y => vol p y u v) := by
  intro x y a b hab
  have hb : b = 1 - a := by linarith
  subst hb; simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma isAffine2_vol1 (q u v : ℝ^3) : IsAffine2 (fun y => vol y q u v) := by
  intro x y a b hab
  have hb : b = 1 - a := by linarith
  subst hb; simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Points of a 3-point hull. -/
lemma mem_convexHull_three {u v w z : ℝ^3}
    (hz : z ∈ convexHull ℝ ({u, v, w} : Set (ℝ^3))) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ z = α • u + β • v + γ • w := by
  rw [convexHull_insert (by simp), convexHull_pair, mem_convexJoin] at hz
  obtain ⟨a, ha, b, hb, hz⟩ := hz
  rw [Set.mem_singleton_iff] at ha
  subst ha
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hb
  obtain ⟨e, f, he, hf, hef, rfl⟩ := hz
  refine ⟨e, f * c, f * d, he, mul_nonneg hf hc, mul_nonneg hf hd, ?_, ?_⟩
  · linear_combination f * hcd + hef
  · rw [smul_add, smul_smul, smul_smul]; abel

/-- The core 5-point lemma: an affine functional vanishing at `u` and positive at `v, w`
vanishes on `conv {u, v, w}` only at `u`. -/
lemma core_zero_only_at {G : ℝ^3 → ℝ} (hG : IsAffine2 G) {u v w z : ℝ^3}
    (hu : G u = 0) (hv : 0 < G v) (hw : 0 < G w)
    (hz : z ∈ convexHull ℝ ({u, v, w} : Set (ℝ^3))) (hGz : G z = 0) : z = u := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := mem_convexHull_three hz
  by_cases hβγ : β + γ = 0
  · have hb : β = 0 := by linarith
    have hc : γ = 0 := by linarith
    have ha : α = 1 := by linarith
    subst hb hc ha; simp
  · have hpos : 0 < β + γ := lt_of_le_of_ne (by linarith) (Ne.symm hβγ)
    exfalso
    have e1 : α • u + β • v + γ • w = α • u + (β + γ) • ((β / (β + γ)) • v + (γ / (β + γ)) • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hβγ, mul_div_cancel₀ _ hβγ, add_assoc]
    rw [e1, hG _ _ α (β + γ) (by linarith), hG _ _ _ _ (by field_simp), hu] at hGz
    have : 0 < (β + γ) * (β / (β + γ) * G v + γ / (β + γ) * G w) := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hβγ, mul_div_cancel₀ _ hβγ]
      rcases eq_or_lt_of_le hβ with hb | hb
      · rw [← hb] at hpos ⊢; simp at hpos; nlinarith
      · nlinarith
    nlinarith

/-! ## Section 11: sign consistency across clusters -/

lemma combo_mem_hull {S : Set (ℝ^3)} {x y : ℝ^3} (hx : x ∈ convexHull ℝ S)
    (hy : y ∈ convexHull ℝ S) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (1 - r) • x + r • y ∈ convexHull ℝ S :=
  convex_convexHull ℝ S hx hy (by linarith) h0 (by ring)

/-- Hypotheses on four clusters in cyclic projected order `A, C, B, D`. -/
def QuadHyp (A C B D : Finset (ℝ^3)) : Prop :=
  (∀ a ∈ A, ∀ c ∈ C, ∀ b ∈ B, ∀ d ∈ D, CCW4 a c b d) ∧
  Disjoint (convexHull ℝ ((A ∪ B : Finset (ℝ^3)) : Set (ℝ^3)))
    (convexHull ℝ ((C ∪ D : Finset (ℝ^3)) : Set (ℝ^3)))

lemma QuadHyp.rot {A C B D : Finset (ℝ^3)} (h : QuadHyp A C B D) : QuadHyp C B D A := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c hc b hb d hd a ha => CCW4_rot (h1 a ha c hc b hb d hd), ?_⟩
  rw [Finset.union_comm B A]
  exact h2.symm

lemma QuadHyp.vol_ne {A C B D : Finset (ℝ^3)} (h : QuadHyp A C B D) {a b c d : ℝ^3}
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (hd : d ∈ D) : vol a b c d ≠ 0 := by
  apply vol_ne_zero (h.1 a ha c hc b hb d hd)
  intro s t hs0 hs1 ht0 ht1 heq
  have hP : (1 - s) • a + s • b ∈ convexHull ℝ ((A ∪ B : Finset (ℝ^3)) : Set (ℝ^3)) :=
    combo_mem_hull (subset_convexHull ℝ _ (by simp [ha])) (subset_convexHull ℝ _ (by simp [hb]))
      hs0 hs1
  have hQ : (1 - t) • c + t • d ∈ convexHull ℝ ((C ∪ D : Finset (ℝ^3)) : Set (ℝ^3)) :=
    combo_mem_hull (subset_convexHull ℝ _ (by simp [hc])) (subset_convexHull ℝ _ (by simp [hd]))
      ht0 ht1
  rw [heq] at hP
  exact Set.disjoint_left.mp h.2 hP hQ

lemma QuadHyp.move_first {A C B D : Finset (ℝ^3)} (h : QuadHyp A C B D) {a a' b c d : ℝ^3}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hc : c ∈ C) (hd : d ∈ D) :
    0 < vol a b c d ↔ 0 < vol a' b c d := by
  apply vol_pos_iff_of_segment (h.1 a ha c hc b hb d hd) (h.1 a' ha' c hc b hb d hd)
  intro r hr0 hr1 s t hs0 hs1 ht0 ht1 heq
  have hR : (1 - r) • a + r • a' ∈ convexHull ℝ ((A ∪ B : Finset (ℝ^3)) : Set (ℝ^3)) :=
    combo_mem_hull (subset_convexHull ℝ _ (by simp [ha])) (subset_convexHull ℝ _ (by simp [ha']))
      hr0 hr1
  have hP : (1 - s) • ((1 - r) • a + r • a') + s • b ∈
      convexHull ℝ ((A ∪ B : Finset (ℝ^3)) : Set (ℝ^3)) :=
    combo_mem_hull hR (subset_convexHull ℝ _ (by simp [hb])) hs0 hs1
  have hQ : (1 - t) • c + t • d ∈ convexHull ℝ ((C ∪ D : Finset (ℝ^3)) : Set (ℝ^3)) :=
    combo_mem_hull (subset_convexHull ℝ _ (by simp [hc])) (subset_convexHull ℝ _ (by simp [hd]))
      ht0 ht1
  rw [heq] at hP
  exact Set.disjoint_left.mp h.2 hP hQ

lemma pos_iff_of_neg_iff {v w : ℝ} (hv : v ≠ 0) (hw : w ≠ 0) (h : 0 < -v ↔ 0 < -w) :
    0 < v ↔ 0 < w := by
  constructor
  · intro hp; by_contra hn
    have : 0 < -w := by have := lt_of_le_of_ne (not_lt.mp hn) hw; linarith
    have := h.mpr this; linarith
  · intro hp; by_contra hn
    have : 0 < -v := by have := lt_of_le_of_ne (not_lt.mp hn) hv; linarith
    have := h.mp this; linarith

/-- The sign of the volume is the same for all choices of points from the four clusters. -/
lemma QuadHyp.sign_const {A C B D : Finset (ℝ^3)} (h : QuadHyp A C B D) {a a' b b' c c' d d' : ℝ^3}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (hc : c ∈ C) (hc' : c' ∈ C)
    (hd : d ∈ D) (hd' : d' ∈ D) :
    0 < vol a b c d ↔ 0 < vol a' b' c' d' := by
  have h1 := h.rot
  have h2 := h1.rot
  have h3 := h2.rot
  have e1 : ∀ a b c d : ℝ^3, vol c d b a = - vol a b c d := fun a b c d => by simp only [vol]; ring
  have e2 : ∀ a b c d : ℝ^3, vol b a d c = vol a b c d := fun a b c d => by simp only [vol]; ring
  have e3 : ∀ a b c d : ℝ^3, vol d c a b = - vol a b c d := fun a b c d => by simp only [vol]; ring
  -- move a
  have s1 : 0 < vol a b c d ↔ 0 < vol a' b c d := h.move_first ha ha' hb hc hd
  -- move c (first point of the rotated configuration `C, B, D, A`)
  have s2 : 0 < vol a' b c d ↔ 0 < vol a' b c' d := by
    have := h1.move_first hc hc' hd hb ha'
    rw [e1 a' b c d, e1 a' b c' d] at this
    exact pos_iff_of_neg_iff (h.vol_ne ha' hb hc hd) (h.vol_ne ha' hb hc' hd) this
  -- move b
  have s3 : 0 < vol a' b c' d ↔ 0 < vol a' b' c' d := by
    have := h2.move_first hb hb' ha' hd hc'
    rwa [e2 a' b c' d, e2 a' b' c' d] at this
  -- move d
  have s4 : 0 < vol a' b' c' d ↔ 0 < vol a' b' c' d' := by
    have := h3.move_first hd hd' hc' ha' hb'
    rw [e3 a' b' c' d, e3 a' b' c' d'] at this
    exact pos_iff_of_neg_iff (h.vol_ne ha' hb' hc' hd) (h.vol_ne ha' hb' hc' hd') this
  exact s1.trans (s2.trans (s3.trans s4))

/-! ## Section 12: separation of alternating arcs of clusters -/

/-- Hypotheses on a sequence of clusters: vertical separation, 2-separation, projected convex
position in counterclockwise order and the "above" pattern for all crossing quadruples. -/
structure ClusterHyp (K : ℕ) (Xs : Fin K → Finset (ℝ^3)) : Prop where
  vsep : ∀ i, ∃ (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ x ∈ Xs i, φ x < c) ∧ (∀ j, j ≠ i → ∀ x ∈ Xs j, c < φ x)
  sep2 : Is2Separated K Xs
  ccw : ∀ a b d : Fin K, a < b → b < d → ∀ x ∈ Xs a, ∀ y ∈ Xs b, ∀ z ∈ Xs d,
    0 < orient2 (projXY x) (projXY y) (projXY z)
  above : ∀ i i' j j' : Fin K, i < i' → i' < j → j < j' →
    ∀ x ∈ Xs i, ∀ x' ∈ Xs i', ∀ y ∈ Xs j, ∀ y' ∈ Xs j', 0 < vol x y x' y'

lemma ClusterHyp.disj {K : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterHyp K Xs)
    {i j : Fin K} (hij : i ≠ j) {x : ℝ^3} (hi : x ∈ Xs i) (hj : x ∈ Xs j) : False := by
  obtain ⟨φ, c, h1, h2⟩ := h.vsep i
  have := h1 x hi
  have := h2 j (Ne.symm hij) x hj
  linarith

lemma orient2_seg_mid (y z : ℝ^3) (s : ℝ) :
    orient2 (projXY y) (projXY ((1 - s) • y + s • z)) (projXY z) = 0 := by
  simp only [orient2_projXY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma orient2_seg_last (y z : ℝ^3) (s : ℝ) :
    orient2 (projXY y) (projXY z) (projXY ((1 - s) • y + s • z)) = 0 := by
  simp only [orient2_projXY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma orient2_seg_first (y z : ℝ^3) (s : ℝ) :
    orient2 (projXY ((1 - s) • y + s • z)) (projXY y) (projXY z) = 0 := by
  simp only [orient2_projXY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma mem_segment_iff' {y z r : ℝ^3} (hr : r ∈ convexHull ℝ ({y, z} : Set (ℝ^3))) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ r = (1 - s) • y + s • z := by
  rw [convexHull_pair] at hr
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hr
  refine ⟨b, hb, by linarith, ?_⟩
  rw [show a = 1 - b by linarith]

lemma orient2_cyc (a b c : ℝ^2) : orient2 b c a = orient2 a b c := by
  unfold orient2; ring

lemma orient2_swap (a b c : ℝ^2) : orient2 a c b = - orient2 a b c := by
  unfold orient2; ring

section ArcSep

variable {K : ℕ} {Xs : Fin K → Finset (ℝ^3)}

/-- Arc separation: if the clusters of `P` occupy an index interval `[L, R)` and those of `Q`
lie outside it, the hulls are disjoint (projected convex position). -/
lemma arc_sep (h : ClusterHyp K Xs) (idx : ℝ^3 → ℕ)
    (hidx : ∀ x (i : Fin K), x ∈ Xs i → idx x = i.val)
    (P Q : Finset (ℝ^3)) (hPm : ∀ y ∈ P, ∃ i, y ∈ Xs i) (hQm : ∀ y ∈ Q, ∃ i, y ∈ Xs i)
    (hinj : Set.InjOn idx (P : Set (ℝ^3))) (hcard : 2 ≤ P.card) (L R : ℕ)
    (hPin : ∀ y ∈ P, L ≤ idx y ∧ idx y < R) (hQout : ∀ z ∈ Q, idx z < L ∨ R ≤ idx z) :
    Disjoint (convexHull ℝ (P : Set (ℝ^3))) (convexHull ℝ (Q : Set (ℝ^3))) := by
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e0, he0, hmin⟩ := P.exists_min_image idx hPne
  obtain ⟨e1, he1, hmax⟩ := P.exists_max_image idx hPne
  obtain ⟨i0, hi0⟩ := hPm e0 he0
  obtain ⟨i1, hi1⟩ := hPm e1 he1
  have hne : e0 ≠ e1 := by
    intro heq
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    have h1 := hmin x hx; have h2 := hmax x hx; have h3 := hmin y hy; have h4 := hmax y hy
    rw [← heq] at h2 h4
    exact hxy (hinj hx hy (by omega))
  have hlt : idx e0 < idx e1 := by
    rcases lt_or_eq_of_le (hmin e1 he1) with h' | h'
    · exact h'
    · exact absurd (hinj he0 he1 h') hne
  have hi01 : i0 < i1 := by
    have := hidx e0 i0 hi0; have := hidx e1 i1 hi1
    rw [Fin.lt_iff_val_lt_val]; omega
  apply disjoint_hulls_of_affine (isAffine2_orient e0 e1)
  · intro y hy
    simp only [Finset.mem_coe] at hy
    by_cases hy0 : y = e0
    · subst hy0; show orient2 (projXY y) (projXY e1) (projXY y) ≤ 0; rw [orient2_self_outer]
    by_cases hy1 : y = e1
    · subst hy1; show orient2 (projXY e0) (projXY y) (projXY y) ≤ 0; rw [orient2_self_right]
    obtain ⟨j, hj⟩ := hPm y hy
    have hmid0 : idx e0 < idx y := lt_of_le_of_ne (hmin y hy) (fun h' => hy0 (hinj hy he0 h'.symm))
    have hmid1 : idx y < idx e1 := lt_of_le_of_ne (hmax y hy) (fun h' => hy1 (hinj hy he1 h'))
    have hj0 : i0 < j := by
      have := hidx e0 i0 hi0; have := hidx y j hj; rw [Fin.lt_iff_val_lt_val]; omega
    have hj1 : j < i1 := by
      have := hidx e1 i1 hi1; have := hidx y j hj; rw [Fin.lt_iff_val_lt_val]; omega
    have := h.ccw i0 j i1 hj0 hj1 e0 hi0 y hj e1 hi1
    show orient2 (projXY e0) (projXY e1) (projXY y) ≤ 0
    rw [orient2_swap]; linarith
  · intro z hz
    simp only [Finset.mem_coe] at hz
    obtain ⟨j, hj⟩ := hQm z hz
    have hzj := hidx z j hj
    have h0 := hidx e0 i0 hi0
    have h1 := hidx e1 i1 hi1
    have hL := (hPin e0 he0).1
    have hR := (hPin e1 he1).2
    show 0 < orient2 (projXY e0) (projXY e1) (projXY z)
    rcases hQout z hz with hz' | hz'
    · have hj0 : j < i0 := by rw [Fin.lt_iff_val_lt_val]; omega
      have := h.ccw j i0 i1 hj0 hi01 z hj e0 hi0 e1 hi1
      rw [orient2_cyc]; exact this
    · have hj1 : i1 < j := by rw [Fin.lt_iff_val_lt_val]; omega
      exact h.ccw i0 i1 j hi01 hj1 e0 hi0 e1 hi1 z hj

end ArcSep

/-- Odd arcs `[0, a) ∪ [b, c)`; the even arcs are `[a, b) ∪ [c, ∞)`. -/
def OddArc (a b c i : ℕ) : Prop := i < a ∨ (b ≤ i ∧ i < c)

instance (a b c i : ℕ) : Decidable (OddArc a b c i) :=
  inferInstanceAs (Decidable (i < a ∨ (b ≤ i ∧ i < c)))

noncomputable def arcUnion {K : ℕ} (Xs : Fin K → Finset (ℝ^3)) (odd : Bool) (a b c : ℕ) : Finset (ℝ^3) :=
  (Finset.univ.filter (fun i : Fin K => OddArc a b c i.val ↔ odd = true)).biUnion Xs

section MainSep

variable {K : ℕ} {Xs : Fin K → Finset (ℝ^3)}

lemma fin_lt_of_idx {idx : ℝ^3 → ℕ} (hidx : ∀ x (i : Fin K), x ∈ Xs i → idx x = i.val)
    {x y : ℝ^3} {i j : Fin K} (hx : x ∈ Xs i) (hy : y ∈ Xs j) (h : idx x < idx y) : i < j := by
  rw [Fin.lt_iff_val_lt_val, ← hidx x i hx, ← hidx y j hy]; exact h

/-- Pick at most two clusters covering a set whose clusters number at most two. -/
lemma pick_two (h : ClusterHyp K Xs) (idx : ℝ^3 → ℕ)
    (hidx : ∀ x (i : Fin K), x ∈ Xs i → idx x = i.val) (P : Finset (ℝ^3)) (Q : Fin K → Prop)
    (hP : ∀ x ∈ P, ∃ i, x ∈ Xs i ∧ Q i) (hne : P.Nonempty) (hcard : (P.image idx).card ≤ 2) :
    ∃ i j, Q i ∧ Q j ∧ P ⊆ Xs i ∪ Xs j := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨i0, hxi0, hQ0⟩ := hP x0 hx0
  by_cases hall : ∀ x ∈ P, x ∈ Xs i0
  · exact ⟨i0, i0, hQ0, hQ0, fun x hx => Finset.mem_union_left _ (hall x hx)⟩
  push_neg at hall
  obtain ⟨x1, hx1, hx1n⟩ := hall
  obtain ⟨i1, hxi1, hQ1⟩ := hP x1 hx1
  have hi01 : idx x0 ≠ idx x1 := by
    rw [hidx x0 i0 hxi0, hidx x1 i1 hxi1]
    intro heq; exact hx1n (Fin.ext heq ▸ hxi1)
  refine ⟨i0, i1, hQ0, hQ1, fun x hx => ?_⟩
  obtain ⟨j, hxj, -⟩ := hP x hx
  by_cases hj0 : j = i0
  · subst hj0; exact Finset.mem_union_left _ hxj
  by_cases hj1 : j = i1
  · subst hj1; exact Finset.mem_union_right _ hxj
  exfalso
  have e0 : idx x ≠ idx x0 := by
    rw [hidx x j hxj, hidx x0 i0 hxi0]; exact fun e => hj0 (Fin.ext e)
  have e1 : idx x ≠ idx x1 := by
    rw [hidx x j hxj, hidx x1 i1 hxi1]; exact fun e => hj1 (Fin.ext e)
  have hsub : ({idx x0, idx x1, idx x} : Finset ℕ) ⊆ P.image idx := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact Finset.mem_image_of_mem _ hx0
    · exact Finset.mem_image_of_mem _ hx1
    · exact Finset.mem_image_of_mem _ hx
  have h3 : ({idx x0, idx x1, idx x} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm e1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hi01, Ne.symm e0⟩
  have := Finset.card_le_card hsub
  omega

lemma image_card_le_one_sub (idx : ℝ^3 → ℕ) (hidx : ∀ x (i : Fin K), x ∈ Xs i → idx x = i.val)
    (P : Finset (ℝ^3)) (hP : ∀ x ∈ P, ∃ i, x ∈ Xs i) (hne : P.Nonempty)
    (hcard : (P.image idx).card ≤ 1) : ∃ i, P ⊆ Xs i := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨i0, hxi0⟩ := hP x0 hx0
  refine ⟨i0, fun x hx => ?_⟩
  obtain ⟨j, hxj⟩ := hP x hx
  have heq : idx x = idx x0 :=
    Finset.card_le_one.mp hcard _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hx0)
  rw [hidx x j hxj, hidx x0 i0 hxi0] at heq
  exact Fin.ext heq ▸ hxj

lemma exists_third {P : Finset (ℝ^3)} (hcard : P.card = 3) {u v : ℝ^3} (hu : u ∈ P) (hv : v ∈ P)
    (huv : u ≠ v) : ∃ w ∈ P, w ≠ u ∧ w ≠ v ∧ P = {u, v, w} := by
  classical
  have h1 : ((P.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩),
      Finset.card_erase_of_mem hu, hcard]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
  have hwm : w ∈ (P.erase u).erase v := by rw [hw]; exact Finset.mem_singleton_self w
  simp only [Finset.mem_erase] at hwm
  refine ⟨w, hwm.2.2, hwm.2.1, hwm.1, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hwm.2.2
  · rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hwm.1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, Ne.symm hwm.2.1⟩

lemma eq_pair_of_card {P : Finset (ℝ^3)} (hcard : P.card = 2) {u v : ℝ^3} (hu : u ∈ P)
    (hv : v ∈ P) (huv : u ≠ v) : P = {u, v} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  · rw [hcard, Finset.card_pair huv]

theorem cluster_arcs_disjoint (h : ClusterHyp K Xs) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    Disjoint (convexHull ℝ ((arcUnion Xs true a b c : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ ((arcUnion Xs false a b c : Finset (ℝ^3)) : Set (ℝ^3))) := by
  classical
  let idx : ℝ^3 → ℕ := fun x => if hx : ∃ i : Fin K, x ∈ Xs i then hx.choose.val else 0
  have hidx : ∀ x (i : Fin K), x ∈ Xs i → idx x = i.val := by
    intro x i hx
    have hex : ∃ i : Fin K, x ∈ Xs i := ⟨i, hx⟩
    simp only [idx, dif_pos hex]
    by_contra hne
    exact h.disj (fun e => hne (congrArg Fin.val e)) hex.choose_spec hx
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hnd
  obtain ⟨A', hA', B', hB', hcard, hne⟩ :=
    kirchberger_finset _ _ (Set.nonempty_iff_ne_empty.mpr hnd)
  have hAm : ∀ x ∈ A', ∃ i, x ∈ Xs i ∧ OddArc a b c i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hA' hx)
    exact ⟨i, hxi, (Finset.mem_filter.mp hi).2.mpr rfl⟩
  have hBm : ∀ x ∈ B', ∃ i, x ∈ Xs i ∧ ¬ OddArc a b c i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hB' hx)
    exact ⟨i, hxi, fun h' => Bool.false_ne_true ((Finset.mem_filter.mp hi).2.mp h')⟩
  have hAm' : ∀ x ∈ A', ∃ i, x ∈ Xs i := fun x hx => (hAm x hx).imp fun _ h => h.1
  have hBm' : ∀ x ∈ B', ∃ i, x ∈ Xs i := fun x hx => (hBm x hx).imp fun _ h => h.1
  have hAodd : ∀ x ∈ A', OddArc a b c (idx x) := fun x hx => by
    obtain ⟨i, hxi, hodd⟩ := hAm x hx; rw [hidx x i hxi]; exact hodd
  have hBeven : ∀ x ∈ B', ¬ OddArc a b c (idx x) := fun x hx => by
    obtain ⟨i, hxi, hodd⟩ := hBm x hx; rw [hidx x i hxi]; exact hodd
  have hidxK : ∀ x ∈ A' ∪ B', idx x < K := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hxi, -⟩ := hAm x hx; rw [hidx x i hxi]; exact i.isLt
    · obtain ⟨i, hxi, -⟩ := hBm x hx; rw [hidx x i hxi]; exact i.isLt
  obtain ⟨r, hrA, hrB⟩ := hne
  have hA'ne : A'.Nonempty := by
    by_contra h0; rw [Finset.not_nonempty_iff_eq_empty] at h0; subst h0; simp at hrA
  have hB'ne : B'.Nonempty := by
    by_contra h0; rw [Finset.not_nonempty_iff_eq_empty] at h0; subst h0; simp at hrB
  -- contradiction from disjoint hulls
  have hcontra : Disjoint (convexHull ℝ (A' : Set (ℝ^3))) (convexHull ℝ (B' : Set (ℝ^3))) →
      False := fun hd => Set.disjoint_left.mp hd hrA hrB
  have hSA := Finset.card_image_le (s := A') (f := idx)
  have hSB := Finset.card_image_le (s := B') (f := idx)
  -- Case 1: both sides meet at most two clusters: 2-separation.
  by_cases hc1 : (A'.image idx).card ≤ 2 ∧ (B'.image idx).card ≤ 2
  · obtain ⟨i, j, hi, hj, hAij⟩ := pick_two h idx hidx A' _ hAm hA'ne hc1.1
    obtain ⟨i', j', hi', hj', hBij⟩ := pick_two h idx hidx B' _ hBm hB'ne hc1.2
    apply hcontra
    have hne' : ∀ p q : Fin K, OddArc a b c p.val → ¬ OddArc a b c q.val → p ≠ q :=
      fun p q hp hq e => hq (e ▸ hp)
    exact (h.sep2 i j i' j' (hne' _ _ hi hi') (hne' _ _ hi hj') (hne' _ _ hj hi')
      (hne' _ _ hj hj')).mono (convexHull_mono (by exact_mod_cast hAij))
      (convexHull_mono (by exact_mod_cast hBij))
  -- Case 2: one side lies in a single cluster: vertical separation.
  have hsingle : ∀ (P Q : Finset (ℝ^3)) (i : Fin K), P ⊆ Xs i → (∀ x ∈ Q, ∃ j, j ≠ i ∧ x ∈ Xs j) →
      Disjoint (convexHull ℝ (P : Set (ℝ^3))) (convexHull ℝ (Q : Set (ℝ^3))) := by
    intro P Q i hPi hQ
    obtain ⟨φ, c0, h1, h2⟩ := h.vsep i
    apply disjoint_hulls_of_affine (isAffine2_linear φ c0)
    · intro x hx; have := h1 x (hPi hx); show φ x - c0 ≤ 0; linarith
    · intro x hx; obtain ⟨j, hji, hxj⟩ := hQ x hx; have := h2 j hji x hxj; show 0 < φ x - c0; linarith
  by_cases hc2 : (B'.image idx).card ≤ 1
  · obtain ⟨i, hBi⟩ := image_card_le_one_sub idx hidx B' hBm' hB'ne hc2
    apply hcontra
    refine (hsingle B' A' i hBi fun x hx => ?_).symm
    obtain ⟨j, hxj, hodd⟩ := hAm x hx
    obtain ⟨y, hy⟩ := hB'ne
    refine ⟨j, fun e => ?_, hxj⟩
    subst e
    exact hBeven y hy (by rw [hidx y j (hBi hy)]; exact hodd)
  by_cases hc3 : (A'.image idx).card ≤ 1
  · obtain ⟨i, hAi⟩ := image_card_le_one_sub idx hidx A' hAm' hA'ne hc3
    apply hcontra
    refine hsingle A' B' i hAi fun x hx => ?_
    obtain ⟨j, hxj, heven⟩ := hBm x hx
    obtain ⟨y, hy⟩ := hA'ne
    refine ⟨j, fun e => ?_, hxj⟩
    subst e
    exact heven (by rw [← hidx y j (hAi hy)]; exact hAodd y hy)
  push_neg at hc2 hc3
  -- Main case: five points from five distinct clusters.
  have hAinj : Set.InjOn idx (A' : Set (ℝ^3)) := by
    rw [← Finset.card_image_iff]
    by_contra hneq
    have := lt_of_le_of_ne hSA hneq
    by_cases hb3 : (B'.image idx).card ≤ 2
    · exact hc1 ⟨by omega, hb3⟩
    · omega
  have hBinj : Set.InjOn idx (B' : Set (ℝ^3)) := by
    rw [← Finset.card_image_iff]
    by_contra hneq
    have := lt_of_le_of_ne hSB hneq
    by_cases ha3 : (A'.image idx).card ≤ 2
    · exact hc1 ⟨ha3, by omega⟩
    · omega
  have hAc2 : 2 ≤ A'.card := by omega
  have hBc2 : 2 ≤ B'.card := by omega
  -- A' meets the first and the third arc, B' meets the second and the fourth.
  have hA1 : ∃ x ∈ A', idx x < a := by
    by_contra hno; push_neg at hno
    apply hcontra
    refine arc_sep h idx hidx A' B' hAm' hBm' hAinj hAc2 b c (fun y hy => ?_) (fun z hz => ?_)
    · have := hno y hy; have := hAodd y hy; unfold OddArc at *; omega
    · have := hBeven z hz; unfold OddArc at *; omega
  have hA3 : ∃ x ∈ A', b ≤ idx x := by
    by_contra hno; push_neg at hno
    apply hcontra
    refine arc_sep h idx hidx A' B' hAm' hBm' hAinj hAc2 0 a (fun y hy => ?_) (fun z hz => ?_)
    · have := hno y hy; have := hAodd y hy; unfold OddArc at *; omega
    · have := hBeven z hz; unfold OddArc at *; omega
  have hB2 : ∃ x ∈ B', idx x < c := by
    by_contra hno; push_neg at hno
    apply hcontra
    refine (arc_sep h idx hidx B' A' hBm' hAm' hBinj hBc2 c K (fun y hy => ?_)
      (fun z hz => ?_)).symm
    · have := hno y hy; have := hidxK y (Finset.mem_union_right _ hy); omega
    · have := hAodd z hz; unfold OddArc at *; omega
  have hB4 : ∃ x ∈ B', c ≤ idx x := by
    by_contra hno; push_neg at hno
    apply hcontra
    refine (arc_sep h idx hidx B' A' hBm' hAm' hBinj hBc2 a b (fun y hy => ?_)
      (fun z hz => ?_)).symm
    · have := hno y hy; have := hBeven y hy; unfold OddArc at *; omega
    · have := hAodd z hz; unfold OddArc at *; omega
  obtain ⟨xp, hxp, hxpa⟩ := hA1
  obtain ⟨xq, hxq, hxqb⟩ := hA3
  obtain ⟨yu, hyu, hyuc⟩ := hB2
  obtain ⟨yv, hyv, hyvc⟩ := hB4
  have hxq' := hAodd xq hxq
  have hyu' := hBeven yu hyu
  unfold OddArc at hxq' hyu'
  have hxqc : idx xq < c := by omega
  have hyua : a ≤ idx yu := by omega
  have hyub : idx yu < b := by omega
  obtain ⟨ip, hip, -⟩ := hAm xp hxp
  obtain ⟨iq, hiq, -⟩ := hAm xq hxq
  obtain ⟨iu, hiu, -⟩ := hBm yu hyu
  obtain ⟨iv, hiv, -⟩ := hBm yv hyv
  have hpu : ip < iu := fin_lt_of_idx hidx hip hiu (by omega)
  have huq : iu < iq := fin_lt_of_idx hidx hiu hiq (by omega)
  have hqv : iq < iv := fin_lt_of_idx hidx hiq hiv (by omega)
  have hxpq : xp ≠ xq := fun e => by subst e; omega
  have hyuv : yu ≠ yv := fun e => by subst e; omega
  rcases (show A'.card = 2 ∧ B'.card = 3 ∨ A'.card = 3 ∧ B'.card = 2 by
      by_cases ha3 : (A'.image idx).card ≤ 2
      · have hb3 : ¬ (B'.image idx).card ≤ 2 := fun hb => hc1 ⟨ha3, hb⟩
        omega
      · omega) with ⟨hA2, hB3⟩ | ⟨hA3', hB2'⟩
  · -- A' = {xp, xq}, B' = {yu, yv, yw}
    have hAeq := eq_pair_of_card hA2 hxp hxq hxpq
    obtain ⟨yw, hyw, hywu, hywv, hBeq⟩ := exists_third hB3 hyu hyv hyuv
    obtain ⟨iw, hiw, -⟩ := hBm yw hyw
    rw [hAeq] at hrA
    rw [hBeq] at hrB
    simp only [Finset.coe_insert, Finset.coe_singleton] at hrA hrB
    obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_iff' hrA
    have hyw' := hBeven yw hyw
    unfold OddArc at hyw'
    by_cases hw4 : c ≤ idx yw
    · -- lone vertex yu in the second arc
      have hqw : iq < iw := fin_lt_of_idx hidx hiq hiw (by omega)
      have hG := core_zero_only_at (isAffine2_vol4 xp xq yu) (by simp only [vol]; ring)
        (h.above ip iu iq iv hpu huq hqv xp hip yu hiu xq hiq yv hiv)
        (h.above ip iu iq iw hpu huq hqw xp hip yu hiu xq hiq yw hiw) hrB
        (by simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
      have := h.ccw ip iu iq hpu huq xp hip yu hiu xq hiq
      rw [← hG, orient2_seg_mid] at this
      exact lt_irrefl _ this
    · -- lone vertex yv in the fourth arc
      have hpw : ip < iw := fin_lt_of_idx hidx hip hiw (by omega)
      have hwq : iw < iq := fin_lt_of_idx hidx hiw hiq (by omega)
      have hrB' : (1 - s) • xp + s • xq ∈ convexHull ℝ ({yv, yu, yw} : Set (ℝ^3)) := by
        rwa [Set.insert_comm]
      have hG := core_zero_only_at (isAffine2_vol3 xp xq yv) (by simp only [vol]; ring)
        (h.above ip iu iq iv hpu huq hqv xp hip yu hiu xq hiq yv hiv)
        (h.above ip iw iq iv hpw hwq hqv xp hip yw hiw xq hiq yv hiv) hrB'
        (by simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
      have := h.ccw ip iq iv (hpu.trans huq) hqv xp hip xq hiq yv hiv
      rw [← hG, orient2_seg_last] at this
      exact lt_irrefl _ this
  · -- B' = {yu, yv}, A' = {xp, xq, xw}
    have hBeq := eq_pair_of_card hB2' hyu hyv hyuv
    obtain ⟨xw, hxw, hxwp, hxwq, hAeq⟩ := exists_third hA3' hxp hxq hxpq
    obtain ⟨iw, hiw, -⟩ := hAm xw hxw
    rw [hAeq] at hrA
    rw [hBeq] at hrB
    simp only [Finset.coe_insert, Finset.coe_singleton] at hrA hrB
    obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_iff' hrB
    have hxw' := hAodd xw hxw
    unfold OddArc at hxw'
    by_cases hw3 : b ≤ idx xw
    · -- lone vertex xp in the first arc
      have huw : iu < iw := fin_lt_of_idx hidx hiu hiw (by omega)
      have hwv : iw < iv := fin_lt_of_idx hidx hiw hiv (by omega)
      have hG := core_zero_only_at (isAffine2_vol2 xp yu yv) (by simp only [vol]; ring)
        (h.above ip iu iq iv hpu huq hqv xp hip yu hiu xq hiq yv hiv)
        (h.above ip iu iw iv hpu huw hwv xp hip yu hiu xw hiw yv hiv) hrA
        (by simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
      have := h.ccw ip iu iv hpu (huq.trans hqv) xp hip yu hiu yv hiv
      rw [← hG, orient2_seg_first] at this
      exact lt_irrefl _ this
    · -- lone vertex xq in the third arc
      have hwu : iw < iu := fin_lt_of_idx hidx hiw hiu (by omega)
      have hrA' : (1 - s) • yu + s • yv ∈ convexHull ℝ ({xq, xp, xw} : Set (ℝ^3)) := by
        rwa [Set.insert_comm]
      have hG := core_zero_only_at (isAffine2_vol1 xq yu yv) (by simp only [vol]; ring)
        (h.above ip iu iq iv hpu huq hqv xp hip yu hiu xq hiq yv hiv)
        (h.above iw iu iq iv hwu huq hqv xw hiw yu hiu xq hiq yv hiv) hrA'
        (by simp only [vol, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
      have := h.ccw iu iq iv huq hqv yu hiu xq hiq yv hiv
      rw [← hG, orient2_seg_mid] at this
      exact lt_irrefl _ this

end MainSep

/-! ## Section 13: Proposition 2.3 for three generic half-spaces -/

/-- The linear map `x ↦ (h 0 x, h 1 x, h 2 x)`. -/
def linOf (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) : (ℝ^3) →ₗ[ℝ] (ℝ^3) where
  toFun x := !₂[h 0 x, h 1 x, h 2 x]
  map_add' x y := by ext k; fin_cases k <;> simp
  map_smul' r x := by ext k; fin_cases k <;> simp

/-- The affine map `x ↦ (h 0 x - γ 0, h 1 x - γ 1, h 2 x - γ 2)`. -/
def affOf (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) : (ℝ^3) →ᵃ[ℝ] (ℝ^3) where
  toFun x := !₂[h 0 x - γ 0, h 1 x - γ 1, h 2 x - γ 2]
  linear := linOf h
  map_vadd' p v := by
    ext k; fin_cases k <;> simp [linOf] <;> ring

lemma affOf_apply (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) (x : ℝ^3) (k : Fin 3) :
    affOf h γ x k = h k x - γ k := by
  fin_cases k <;> simp [affOf]

lemma affOf_combo (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) (x y : ℝ^3) (t : ℝ) :
    (1 - t) • affOf h γ x + t • affOf h γ y = affOf h γ ((1 - t) • x + t • y) := by
  ext k
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, affOf_apply, map_add, map_smul]
  ring

lemma affOf_mem_posOctant {h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ} {γ : Fin 3 → ℝ} {x : ℝ^3} :
    affOf h γ x ∈ PosOctant ↔ ∀ k, γ k ≤ h k x := by
  simp only [PosOctant, Set.mem_setOf_eq, affOf_apply, sub_nonneg]
  constructor
  · rintro ⟨h0, h1, h2⟩ k; fin_cases k
    · exact h0
    · exact h1
    · exact h2
  · intro hk; exact ⟨hk 0, hk 1, hk 2⟩

lemma orient2_proj3_affOf (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) (i : Fin 3) (x y z : ℝ^3) :
    ∃ j k : Fin 3, j ≠ k ∧
      orient2 (proj3 i (affOf h γ x)) (proj3 i (affOf h γ y)) (proj3 i (affOf h γ z)) =
        h j (y - x) * h k (z - x) - h j (z - x) * h k (y - x) := by
  fin_cases i
  · refine ⟨1, 2, by decide, ?_⟩
    simp [proj3, orient2, affOf, map_sub]; ring
  · refine ⟨0, 2, by decide, ?_⟩
    simp [proj3, orient2, affOf, map_sub]; ring
  · refine ⟨0, 1, by decide, ?_⟩
    simp [proj3, orient2, affOf, map_sub]; ring

lemma proj3_eq_coord (i : Fin 3) (u v : ℝ^3) (h : proj3 i u = proj3 i v) :
    ∃ k : Fin 3, u k = v k := by
  fin_cases i
  · refine ⟨1, ?_⟩
    have := congrFun (congrArg (fun w : ℝ^2 => (w : Fin 2 → ℝ)) h) 0
    simpa [proj3] using this
  · refine ⟨0, ?_⟩
    have := congrFun (congrArg (fun w : ℝ^2 => (w : Fin 2 → ℝ)) h) 0
    simpa [proj3] using this
  · refine ⟨0, ?_⟩
    have := congrFun (congrArg (fun w : ℝ^2 => (w : Fin 2 → ℝ)) h) 0
    simpa [proj3] using this

lemma proj3_affOf_notMem (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) (x : ℝ^3)
    (hs : h 0 x < γ 0 ∧ (h 1 x < γ 1 ∨ h 2 x < γ 2)) (i : Fin 3) :
    proj3 i (affOf h γ x) ∉ PosQuad := by
  obtain ⟨h0, h12⟩ := hs
  intro hq
  simp only [PosQuad, Set.mem_setOf_eq] at hq
  fin_cases i
  · simp only [proj3, affOf] at hq
    simp at hq
    rcases h12 with h1 | h2
    · linarith [hq.1]
    · linarith [hq.2]
  · simp only [proj3, affOf] at hq
    simp at hq
    linarith [hq.1]
  · simp only [proj3, affOf] at hq
    simp at hq
    linarith [hq.1]

/-- Proposition 2.3 for the polyhedron `P = {x | ∀ k, γ k ≤ h k x}` with generic functionals. -/
theorem halfspace_cups_caps (Z : Finset (ℝ^3)) (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ)
    (hinj : ∀ k, ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → h k x ≠ h k y)
    (hgp : ∀ j k : Fin 3, j ≠ k → ∀ x ∈ Z, ∀ y ∈ Z, ∀ z ∈ Z, x ≠ y → y ≠ z → x ≠ z →
      h j (y - x) * h k (z - x) - h j (z - x) * h k (y - x) ≠ 0)
    (hsign : ∀ x ∈ Z, h 0 x < γ 0 ∧ (h 1 x < γ 1 ∨ h 2 x < γ 2))
    (hfree : IsCFree {x | ∀ k, γ k ≤ h k x} Z)
    (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : (Nat.choose (a + b - 4) (a - 2)) ^ 3 < Z.card) :
    (∃ Kc ⊆ Z, Kc.card = a ∧ IsCCap {x | ∀ k, γ k ≤ h k x} Kc) ∨ Erdos651.HasConvexSubset b Z := by
  classical
  set A := affOf h γ with hA
  set P : Set (ℝ^3) := {x | ∀ k, γ k ≤ h k x} with hP
  have hAinj : Set.InjOn A (Z : Set (ℝ^3)) := by
    intro x hx y hy hxy
    by_contra hne
    apply hinj 0 x hx y hy hne
    have := congrFun (congrArg (fun w : ℝ^3 => (w : Fin 3 → ℝ)) hxy) 0
    simp only [hA] at this
    have e1 := affOf_apply h γ x 0
    have e2 := affOf_apply h γ y 0
    simp only [WithLp.ofLp] at e1 e2
    linarith
  have hmemimg : ∀ x' ∈ Z.image A, ∃ x ∈ Z, A x = x' := fun x' hx' => Finset.mem_image.mp hx'
  -- coordinate injectivity of the image
  have hcoord : ∀ k : Fin 3, Set.InjOn (fun x : ℝ^3 => x k) ((Z.image A : Finset (ℝ^3)) : Set (ℝ^3)) := by
    intro k x' hx' y' hy' hxy
    obtain ⟨x, hx, rfl⟩ := hmemimg x' hx'
    obtain ⟨y, hy, rfl⟩ := hmemimg y' hy'
    by_cases hne : x = y
    · rw [hne]
    · exfalso; apply hinj k x hx y hy hne
      simp only [hA, affOf_apply] at hxy; linarith
  refine (orthant_cups_caps a b ha hb (Z.image A) ?free ?disj ?pinj ?pgp hcoord ?card).imp ?c1 ?c2
  case free =>
    intro x' hx' y' hy' hne t hmem
    obtain ⟨x, hx, rfl⟩ := hmemimg x' hx'
    obtain ⟨y, hy, rfl⟩ := hmemimg y' hy'
    have hxy : x ≠ y := fun e => hne (by rw [e])
    rw [affOf_combo, affOf_mem_posOctant] at hmem
    exact hfree x hx y hy hxy t hmem
  case disj =>
    intro i x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemimg x' hx'
    exact proj3_affOf_notMem h γ x (hsign x hx) i
  case pinj =>
    intro i x' hx' y' hy' hxy
    obtain ⟨k, hk⟩ := proj3_eq_coord i x' y' hxy
    exact hcoord k hx' hy' hk
  case pgp =>
    intro i p hp q hq r hr hpq hqr hpr
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨x, hx, rfl⟩ := hmemimg x' hx'
    obtain ⟨y, hy, rfl⟩ := hmemimg y' hy'
    obtain ⟨z, hz, rfl⟩ := hmemimg z' hz'
    obtain ⟨j, k, hjk, he⟩ := orient2_proj3_affOf h γ i x y z
    rw [he]
    exact hgp j k hjk x hx y hy z hz (fun e => hpq (by rw [e])) (fun e => hqr (by rw [e]))
      (fun e => hpr (by rw [e]))
  case card =>
    rwa [Finset.card_image_of_injOn hAinj]
  case c1 =>
    rintro ⟨K', hK'sub, hK'card, hcap⟩
    refine ⟨Z.filter (fun x => A x ∈ K'), Finset.filter_subset _ _, ?_, ?_⟩
    · have himg : (Z.filter (fun x => A x ∈ K')).image A = K' := by
        ext x'; constructor
        · intro hx'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
          exact (Finset.mem_filter.mp hx).2
        · intro hx'; obtain ⟨x, hx, rfl⟩ := hmemimg x' (hK'sub hx')
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hx'⟩)
      have hc := Finset.card_image_of_injOn (hAinj.mono (by
        intro x hx; exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1) :
          Set.InjOn A ((Z.filter (fun x => A x ∈ K') : Finset (ℝ^3)) : Set (ℝ^3)))
      rw [himg] at hc; omega
    · intro x hx hmem
      have hxZ := (Finset.mem_filter.mp hx).1
      have hAx := (Finset.mem_filter.mp hx).2
      apply hcap (A x) hAx
      have h1 : A x ∈ A '' convexHull ℝ (P ∪ (((Z.filter (fun x => A x ∈ K')).erase x :
          Finset (ℝ^3)) : Set (ℝ^3))) := ⟨x, hmem, rfl⟩
      rw [AffineMap.image_convexHull] at h1
      refine convexHull_mono ?_ h1
      rintro _ ⟨w, hw | hw, rfl⟩
      · left; exact affOf_mem_posOctant.mpr hw
      · right
        have hw' := Finset.mem_erase.mp (Finset.mem_coe.mp hw)
        have hwZ := (Finset.mem_filter.mp hw'.2).1
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun e => hw'.1 (hAinj hwZ hxZ e),
          (Finset.mem_filter.mp hw'.2).2⟩)
  case c2 =>
    rintro ⟨W', hW'sub, hW'card, hW'conv⟩
    have himg : (Z.filter (fun x => A x ∈ W')).image A = W' := by
      ext x'; constructor
      · intro hx'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
        exact (Finset.mem_filter.mp hx).2
      · intro hx'; obtain ⟨x, hx, rfl⟩ := hmemimg x' (hW'sub hx')
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hx'⟩)
    have hinjW : Set.InjOn A ((Z.filter (fun x => A x ∈ W') : Finset (ℝ^3)) : Set (ℝ^3)) :=
      hAinj.mono (by intro x hx; exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
    refine ⟨Z.filter (fun x => A x ∈ W'), Finset.filter_subset _ _, ?_, ?_⟩
    · have hc := Finset.card_image_of_injOn hinjW
      rw [himg] at hc; omega
    · rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hW'conv ⊢
      intro x hx hmem
      have hxW := Finset.mem_coe.mp hx
      apply hW'conv (A x) (Finset.mem_coe.mpr (Finset.mem_filter.mp hxW).2)
      have h1 : A x ∈ A '' convexHull ℝ (((Z.filter (fun x => A x ∈ W') : Finset (ℝ^3)) :
          Set (ℝ^3)) \ {x}) := ⟨x, hmem, rfl⟩
      rw [AffineMap.image_convexHull] at h1
      refine convexHull_mono ?_ h1
      rintro _ ⟨w, ⟨hw, hwx⟩, rfl⟩
      refine ⟨Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2, ?_⟩
      intro e
      exact hwx (hinjW hw hx e)

/-! ## Section 14: the order `≺_P`, free sets and unions of caps -/

def precR (P : Set (ℝ^3)) (x y : ℝ^3) : Prop :=
  x = y ∨ ∃ l : ℝ, ∃ p ∈ P, 0 ≤ l ∧ l < 1 ∧ x = l • y + (1 - l) • p

lemma precR_refl (P : Set (ℝ^3)) (x : ℝ^3) : precR P x x := Or.inl rfl

lemma precR_trans {P : Set (ℝ^3)} (hP : Convex ℝ P) {x y z : ℝ^3}
    (hxy : precR P x y) (hyz : precR P y z) : precR P x z := by
  rcases hxy with rfl | ⟨l, p, hp, hl0, hl1, rfl⟩
  · exact hyz
  rcases hyz with rfl | ⟨m, q, hq, hm0, hm1, rfl⟩
  · exact Or.inr ⟨l, p, hp, hl0, hl1, rfl⟩
  right
  have hL : l * m < 1 := by nlinarith
  have hpos : 0 < 1 - l * m := by linarith
  refine ⟨l * m, (l * (1 - m) / (1 - l * m)) • q + ((1 - l) / (1 - l * m)) • p,
    hP hq hp (div_nonneg (by nlinarith) hpos.le) (div_nonneg (by linarith) hpos.le) ?_,
    mul_nonneg hl0 hm0, hL, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hpos.ne']; ring
  · ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring

lemma precR_antisymm {P : Set (ℝ^3)} (hP : Convex ℝ P) {x y : ℝ^3} (hx : x ∉ P)
    (hxy : precR P x y) (hyx : precR P y x) : x = y := by
  rcases hxy with h | ⟨l, p, hp, hl0, hl1, hxe⟩
  · exact h
  rcases hyx with h | ⟨m, q, hq, hm0, hm1, hye⟩
  · exact h.symm
  exfalso
  apply hx
  have hpos : 0 < 1 - l * m := by nlinarith
  have hx' : x = (l * (1 - m) / (1 - l * m)) • q + ((1 - l) / (1 - l * m)) • p := by
    have e : (1 - l * m) • x = (l * (1 - m)) • q + (1 - l) • p := by
      have h2 := hxe
      rw [hye] at h2
      linear_combination (norm := module) h2
    have := congrArg (fun v => (1 - l * m)⁻¹ • v) e
    simp only [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, smul_add] at this
    rw [this, div_eq_inv_mul, div_eq_inv_mul]
  rw [hx']
  exact hP hq hp (div_nonneg (by nlinarith) hpos.le) (div_nonneg (by linarith) hpos.le)
    (by rw [← add_div, div_eq_one_iff_eq hpos.ne']; ring)

/-- Antichains of `≺_P` are `P`-free, provided `S` and `P` are separated by a hyperplane. -/
lemma free_of_antichain {P : Set (ℝ^3)} {S : Finset (ℝ^3)} (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ)
    (hS : ∀ x ∈ S, φ x < c) (hPφ : ∀ p ∈ P, c ≤ φ p)
    (hanti : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ precR P x y) : IsCFree P S := by
  intro x hx y hy hxy t hmem
  have hval : φ ((1 - t) • x + t • y) = (1 - t) * φ x + t * φ y := by
    simp [map_add, map_smul]
  have hge := hPφ _ hmem
  rw [hval] at hge
  have h1 := hS x hx
  have h2 := hS y hy
  rcases lt_or_ge 1 t with ht | ht
  · -- y lies between x and the point of P
    apply hanti y hy x hx (Ne.symm hxy)
    right
    refine ⟨1 - 1 / t, (1 - t) • x + t • y, hmem, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · have : 0 < 1 / t := by positivity
      linarith
    · have htne : t ≠ 0 := by linarith
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
  rcases lt_or_ge t 0 with ht0 | ht0
  · -- x lies between the point of P and y
    apply hanti x hx y hy hxy
    right
    have hpos : 0 < 1 - t := by linarith
    refine ⟨-t / (1 - t), (1 - t) • x + t • y, hmem, div_nonneg (by linarith) hpos.le,
      (div_lt_one hpos).mpr (by linarith), ?_⟩
    have hne : 1 - t ≠ 0 := hpos.ne'
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have e : (1 - t) * φ x + t * φ y - c = (1 - t) * (φ x - c) + t * (φ y - c) := by ring
    have hA : (1 - t) * (φ x - c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0] at hge; linarith
    · have hB : t * (φ y - c) < 0 := mul_neg_of_pos_of_neg h0 (by linarith)
      linarith

/-- Three convex-like sets each strictly separated from the union of the other two by a
hyperplane: no line meets all three. Used to show that chains of `≺_P` are `Q`-free. -/
lemma free_of_chain {P Q : Set (ℝ^3)} {S : Finset (ℝ^3)}
    (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ) (hφS : ∀ x ∈ S, φ x < c) (hφP : ∀ p ∈ P, c < φ p)
    (hφQ : ∀ q ∈ Q, c < φ q)
    (ψ : (ℝ^3) →ₗ[ℝ] ℝ) (d : ℝ) (hψP : ∀ p ∈ P, d < ψ p) (hψS : ∀ x ∈ S, ψ x < d)
    (hψQ : ∀ q ∈ Q, ψ q < d)
    (χ : (ℝ^3) →ₗ[ℝ] ℝ) (e : ℝ) (hχQ : ∀ q ∈ Q, e < χ q) (hχS : ∀ x ∈ S, χ x < e)
    (hχP : ∀ p ∈ P, χ p < e)
    (hchain : ∀ x ∈ S, ∀ y ∈ S, precR P x y ∨ precR P y x) : IsCFree Q S := by
  -- key claim for an ordered pair
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → precR P x y → ∀ t : ℝ, (1 - t) • x + t • y ∉ Q := by
    intro x hx y hy hxy hpre t hq
    rcases hpre with h | ⟨l, p, hp, hl0, hl1, hxe⟩
    · exact hxy h
    have hpos : 0 < 1 - l := by linarith
    -- p = (1 - r) • x + r • y with r = -l / (1 - l) ≤ 0
    set r := -l / (1 - l) with hr
    have hr0 : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    have hpe : p = (1 - r) • x + r • y := by
      have h1 : (1 - l) • p = x - l • y := by linear_combination (norm := module) -hxe
      have h2 : p = (1 - l)⁻¹ • (x - l • y) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      rw [h2, hr, smul_sub, smul_smul]
      rw [show 1 - -l / (1 - l) = (1 - l)⁻¹ by field_simp; ring,
        show -l / (1 - l) = -((1 - l)⁻¹ * l) by field_simp]
      module
    have lin : ∀ f : (ℝ^3) →ₗ[ℝ] ℝ, ∀ s : ℝ, f ((1 - s) • x + s • y) = f x + s * (f y - f x) := by
      intro f s; simp [map_add, map_smul]; ring
    have hφp := hφP p hp; rw [hpe, lin] at hφp
    have hψp := hψP p hp; rw [hpe, lin] at hψp
    have hχp := hχP p hp; rw [hpe, lin] at hχp
    have hφq := hφQ _ hq; rw [lin] at hφq
    have hψq := hψQ _ hq; rw [lin] at hψq
    have hχq := hχQ _ hq; rw [lin] at hχq
    have a1 := hφS x hx; have a2 := hφS y hy
    have b1 := hψS x hx; have b2 := hψS y hy
    have c1 := hχS x hx; have c2 := hχS y hy
    -- from φ: r < 0 and φ y < φ x, hence t < 0
    have hrneg : r < 0 := by
      rcases lt_or_eq_of_le hr0 with h | h
      · exact h
      · rw [h] at hφp; linarith
    have hφd : φ y - φ x < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have htneg : t < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    -- from ψ: ψ y < ψ x and r < t
    have hψd : ψ y - ψ x < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have hrt : r < t := by
      by_contra hc; push_neg at hc; nlinarith
    -- from χ: χ y < χ x and t < r
    have hχd : χ y - χ x < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have htr : t < r := by
      by_contra hc; push_neg at hc; nlinarith
    linarith
  intro x hx y hy hxy t hq
  rcases hchain x hx y hy with h | h
  · exact key x hx y hy hxy h t hq
  · apply key y hy x hx (Ne.symm hxy) h (1 - t)
    rw [show (1 - (1 - t)) • y + (1 - t) • x = (1 - t) • x + t • y by module]
    exact hq

/-- A union of caps, each lying inside the others' polyhedra, is in convex position. -/
lemma union_caps_convex {ι : Type*} [DecidableEq ι] (I : Finset ι) (Kf : ι → Finset (ℝ^3))
    (P : ι → Set (ℝ^3)) (hcap : ∀ l ∈ I, IsCCap (P l) (Kf l))
    (hin : ∀ l ∈ I, ∀ m ∈ I, m ≠ l → ((Kf m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P l) :
    ConvexIndependent ℝ ((↑) : ↥((I.biUnion Kf : Finset (ℝ^3)) : Set (ℝ^3)) → ℝ^3) := by
  classical
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro x hx hmem
  obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
  apply hcap l hl x hxl
  refine convexHull_mono ?_ hmem
  rintro y ⟨hy, hyx⟩
  obtain ⟨m, hm, hym⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
  by_cases hml : m = l
  · subst hml
    right
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyx, hym⟩)
  · left
    exact hin l hl m hm hml hym

lemma hasConvexSubset_of_convex {X S : Finset (ℝ^3)} {n : ℕ} (hSX : S ⊆ X) (hn : n ≤ S.card)
    (hS : ConvexIndependent ℝ ((↑) : ↥(S : Set (ℝ^3)) → ℝ^3)) : Erdos651.HasConvexSubset n X := by
  obtain ⟨W, hWS, hWcard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨W, hWS.trans hSX, hWcard, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hS ⊢
  intro x hx hmem
  exact hS x (Finset.mem_coe.mpr (hWS (Finset.mem_coe.mp hx)))
    (convexHull_mono (Set.diff_subset_diff_left (by exact_mod_cast hWS)) hmem)


/-! ## Section 15: helper lemmas (final bound, generic choice) -/


/-! ## Lemma 1: final asymptotic bound -/

theorem choose_mul_pow_le (N k t : ℕ) (hk : k ≤ N) :
    N.choose k * t ^ (N - k) ≤ (t + 1) ^ N := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  calc N.choose k * t ^ (N - k) = t ^ (N - k) * N.choose (N - k) := by
        rw [Nat.choose_symm hk, mul_comm]
    _ ≤ ∑ m ∈ Finset.range (N + 1), t ^ m * N.choose m :=
      Finset.single_le_sum (f := fun m => t ^ m * N.choose m) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))

theorem pz_final_bound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 2 ≤ t → ∀ D : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
    (D : ℝ) * ((Nat.choose ((n + t - 1) / t + n - 4) ((n + t - 1) / t - 2) : ℕ) : ℝ) ^ 6
      ≤ (t : ℝ) ^ (C * n / t) := by
  refine ⟨25, by norm_num, fun t ht D => ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨2 * D * t + 2 * t, fun n hn => ?_⟩
  have htpos : 0 < t := by omega
  have hn2t : 2 * t ≤ n := le_trans (Nat.le_add_left _ _) hn
  have hnD : 2 * D * t ≤ n := le_trans (Nat.le_add_right _ _) hn
  obtain ⟨a, ha_def⟩ : ∃ a, a = (n + t - 1) / t := ⟨_, rfl⟩
  rw [← ha_def]
  have ha2 : 2 ≤ a := by
    rw [ha_def, Nat.le_div_iff_mul_le htpos]; omega
  have hat : a * t ≤ n + t - 1 := by rw [ha_def]; exact Nat.div_mul_le_self _ _
  have hat' : a * t + 1 ≤ n + t := by omega
  obtain ⟨k, hk⟩ : ∃ k, k = a - 2 := ⟨_, rfl⟩
  have hNeq : a + n - 4 = k + (n - 2) := by omega
  have hkN : k ≤ k + (n - 2) := Nat.le_add_right _ _
  rw [hNeq, ← hk]
  have hB := choose_mul_pow_le (k + (n - 2)) k t hkN
  rw [show k + (n - 2) - k = n - 2 by omega] at hB
  have hT : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hTpos : (0:ℝ) < t := by linarith
  have hL : (1/2:ℝ) ≤ Real.log t := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) hT
    linarith
  have hy0 : (0:ℝ) ≤ n / t := by positivity
  have hBR : ((Nat.choose (k + (n - 2)) k : ℕ) : ℝ) * (t:ℝ) ^ (n - 2)
      ≤ ((t:ℝ) + 1) ^ k * ((t:ℝ) + 1) ^ (n - 2) := by
    rw [← pow_add]; exact_mod_cast hB
  have hexpL : Real.exp (2 * Real.log t) = (t:ℝ) ^ 2 := by
    rw [show 2 * Real.log t = Real.log t + Real.log t by ring, Real.exp_add, Real.exp_log hTpos]
    ring
  have hB1 : (t:ℝ) + 1 ≤ Real.exp (2 * Real.log t) := by rw [hexpL]; nlinarith
  have hkR : (k:ℝ) = (a:ℝ) - 2 := by rw [hk, Nat.cast_sub ha2]; norm_num
  have hatR : (a:ℝ) * t + 1 ≤ n + t := by exact_mod_cast hat'
  have hk_le : (k:ℝ) ≤ n / t := by
    rw [le_div_iff₀ hTpos, hkR]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (2 * Real.log t * (n / t)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hP : ((t:ℝ) + 1) ^ k ≤ E := by
    rw [hE]
    calc ((t:ℝ) + 1) ^ k ≤ Real.exp (2 * Real.log t) ^ k :=
          pow_le_pow_left₀ (by positivity) hB1 k
      _ = Real.exp (k * (2 * Real.log t)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (2 * Real.log t * (n / t)) := by
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hk_le (by linarith : (0:ℝ) ≤ 2 * Real.log t)]
  have hm_le : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  have hQ : ((t:ℝ) + 1) ^ (n - 2) ≤ E * (t:ℝ) ^ (n - 2) := by
    have h1 : ((t:ℝ) + 1) ^ (n - 2) = (t:ℝ) ^ (n - 2) * (1 + 1 / (t:ℝ)) ^ (n - 2) := by
      rw [← mul_pow, mul_add, mul_one_div_cancel hTpos.ne']; ring
    have h2 : (1 + 1 / (t:ℝ)) ^ (n - 2) ≤ E := by
      rw [hE]
      calc (1 + 1 / (t:ℝ)) ^ (n - 2) ≤ Real.exp (1 / t) ^ (n - 2) := by
            apply pow_le_pow_left₀ (by positivity)
            have := Real.add_one_le_exp (1 / (t:ℝ)); linarith
        _ = Real.exp (((n - 2 : ℕ) : ℝ) * (1 / t)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (2 * Real.log t * (n / t)) := by
            apply Real.exp_le_exp.2
            have h3 : ((n - 2 : ℕ) : ℝ) * (1 / t) ≤ n / t := by
              rw [mul_one_div]; exact div_le_div_of_nonneg_right hm_le hTpos.le
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log t - 1) hy0]
    rw [h1, mul_comm]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hm_pos : (0:ℝ) < (t:ℝ) ^ (n - 2) := by positivity
  have hBle : ((Nat.choose (k + (n - 2)) k : ℕ) : ℝ) ≤ E * E := by
    have : ((Nat.choose (k + (n - 2)) k : ℕ) : ℝ) * (t:ℝ) ^ (n - 2)
        ≤ (E * E) * (t:ℝ) ^ (n - 2) := by
      calc _ ≤ ((t:ℝ) + 1) ^ k * ((t:ℝ) + 1) ^ (n - 2) := hBR
        _ ≤ E * (E * (t:ℝ) ^ (n - 2)) := mul_le_mul hP hQ (by positivity) hE0
        _ = (E * E) * (t:ℝ) ^ (n - 2) := by ring
    exact le_of_mul_le_mul_right this hm_pos
  have hDR : (2 * D * t : ℝ) ≤ n := by exact_mod_cast hnD
  have hyD : (2 * D : ℝ) ≤ n / t := by rw [le_div_iff₀ hTpos]; linarith
  have hD : (D:ℝ) ≤ Real.exp (Real.log t * (n / t)) := by
    have := Real.add_one_le_exp (Real.log t * (n / t))
    nlinarith [mul_le_mul_of_nonneg_right hL hy0]
  rw [Real.rpow_def_of_pos hTpos]
  have hB6 : ((Nat.choose (k + (n - 2)) k : ℕ) : ℝ) ^ 6 ≤ (E * E) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hBle 6
  calc (D:ℝ) * ((Nat.choose (k + (n - 2)) k : ℕ) : ℝ) ^ 6
      ≤ Real.exp (Real.log t * (n / t)) * (E * E) ^ 6 :=
        mul_le_mul hD hB6 (by positivity) (by positivity)
    _ = Real.exp (Real.log t * (25 * n / t)) := by
        rw [hE, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring

/-! ## Lemma 2: generic choice of three linear functionals -/

def lf (F : Fin 3 → Fin 3 → ℝ) (k : Fin 3) (x : ℝ^3) : ℝ := ∑ i, F k i * x i

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_ne_zero_of_open {f : E → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) {G : E}
    (hG : f G ≠ 0) {O : Set E} (hO : IsOpen O) {x0 : E} (hx0 : x0 ∈ O) :
    ∃ x ∈ O, f x ≠ 0 := by
  by_contra h
  push_neg at h
  have hev : f =ᶠ[nhds x0] 0 := by
    filter_upwards [hO.mem_nhds hx0] with x hx using h x hx
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ x0) hev
  exact hG (this (Set.mem_univ G))

theorem refine_open {ι : Type*} [DecidableEq ι] (f : ι → E → ℝ) (s : Finset ι) :
    (∀ i ∈ s, AnalyticOnNhd ℝ (f i) Set.univ) → (∀ i ∈ s, ∃ G, f i G ≠ 0) →
    ∀ O : Set E, IsOpen O → (∃ x, x ∈ O) →
      ∃ O' : Set E, IsOpen O' ∧ (∃ x, x ∈ O') ∧ O' ⊆ O ∧ ∀ x ∈ O', ∀ i ∈ s, f i x ≠ 0 := by
  refine Finset.induction_on s ?_ ?_
  · intro _ _ O hO hne
    exact ⟨O, hO, hne, subset_rfl, by simp⟩
  · intro a s _ ih hf hG O hO hne
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨G, hGa⟩ := hG a (Finset.mem_insert_self a s)
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨x1, hx1, hfx1⟩ := exists_ne_zero_of_open hfa hGa hO hx0
    have hO1 : IsOpen (O ∩ {x | f a x ≠ 0}) :=
      hO.inter (isOpen_ne_fun (continuousOn_univ.1 hfa.continuousOn) continuous_const)
    obtain ⟨O', hO', hne', hsub, hprop⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hG i (Finset.mem_insert_of_mem hi)) _ hO1 ⟨x1, hx1, hfx1⟩
    refine ⟨O', hO', hne', fun x hx => (hsub hx).1, fun x hx i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (hsub hx).2
    · exact hprop x hx i hi

end Generic

theorem analytic_entry (k i : Fin 3) :
    AnalyticOnNhd ℝ (fun F : Fin 3 → Fin 3 → ℝ => F k i) Set.univ := by
  intro F _
  have : (fun F : Fin 3 → Fin 3 → ℝ => F k i) =
      ⇑((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj k : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))) := by
    funext F; rfl
  rw [this]; exact ContinuousLinearMap.analyticAt _ _

theorem analytic_lf (k : Fin 3) (x : ℝ^3) :
    AnalyticOnNhd ℝ (fun F : Fin 3 → Fin 3 → ℝ => lf F k x) Set.univ := by
  unfold lf
  exact Finset.analyticOnNhd_fun_sum _ (fun i _ => (analytic_entry k i).mul analyticOnNhd_const)

theorem analytic_det :
    AnalyticOnNhd ℝ (fun F : Fin 3 → Fin 3 → ℝ => Matrix.det (Matrix.of F)) Set.univ := by
  have e : ∀ a b : Fin 3, AnalyticOnNhd ℝ (fun F : Fin 3 → Fin 3 → ℝ => F a b) Set.univ :=
    analytic_entry
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  exact ((((((e 0 0).mul (e 1 1)).mul (e 2 2)).sub (((e 0 0).mul (e 1 2)).mul (e 2 1))).sub
    (((e 0 1).mul (e 1 0)).mul (e 2 2))).add (((e 0 1).mul (e 1 2)).mul (e 2 0))).add
    (((e 0 2).mul (e 1 0)).mul (e 2 1)) |>.sub (((e 0 2).mul (e 1 1)).mul (e 2 0))

theorem analytic_minor (j k : Fin 3) (w : (ℝ^3) × (ℝ^3)) :
    AnalyticOnNhd ℝ (fun F : Fin 3 → Fin 3 → ℝ =>
      lf F j w.1 * lf F k w.2 - lf F j w.2 * lf F k w.1) Set.univ :=
  ((analytic_lf j w.1).mul (analytic_lf k w.2)).sub ((analytic_lf j w.2).mul (analytic_lf k w.1))

/-- The row-selector matrix: row `k` is the standard basis covector `e_(r k)`. -/
def sel (r : Fin 3 → Fin 3) : Fin 3 → Fin 3 → ℝ := fun k i => if i = r k then 1 else 0

theorem lf_sel (r : Fin 3 → Fin 3) (k : Fin 3) (x : ℝ^3) : lf (sel r) k x = x (r k) := by
  unfold lf sel
  simp

theorem exists_minor_ne (w : (ℝ^3) × (ℝ^3))
    (hw : ∀ a b : ℝ, a • w.1 + b • w.2 = 0 → a = 0 ∧ b = 0) :
    ∃ i i' : Fin 3, w.1 i * w.2 i' - w.2 i * w.1 i' ≠ 0 := by
  by_contra h
  push_neg at h
  by_cases h1 : ∃ i0, w.1 i0 ≠ 0
  · obtain ⟨i0, hi0⟩ := h1
    have hz : (w.2 i0) • w.1 + (-(w.1 i0)) • w.2 = 0 := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul]
      have := h i0 i
      linarith
    exact hi0 (neg_eq_zero.1 (hw _ _ hz).2)
  · push_neg at h1
    have hz : (1:ℝ) • w.1 + (0:ℝ) • w.2 = 0 := by
      ext i
      simp [h1 i]
    exact one_ne_zero (hw _ _ hz).1

theorem generic_choice (F0 : Fin 3 → Fin 3 → ℝ) (S : Finset (Fin 3 × (ℝ^3) × (ℝ^3)))
    (hS : ∀ p ∈ S, lf F0 p.1 p.2.1 < lf F0 p.1 p.2.2)
    (V : Finset (ℝ^3)) (hV : ∀ v ∈ V, v ≠ 0)
    (W : Finset ((ℝ^3) × (ℝ^3)))
    (hW : ∀ w ∈ W, ∀ a b : ℝ, a • w.1 + b • w.2 = 0 → a = 0 ∧ b = 0) :
    ∃ F : Fin 3 → Fin 3 → ℝ,
      (∀ p ∈ S, lf F p.1 p.2.1 < lf F p.1 p.2.2) ∧
      Matrix.det (Matrix.of F) ≠ 0 ∧
      (∀ k, ∀ v ∈ V, lf F k v ≠ 0) ∧
      (∀ j k, j ≠ k → ∀ w ∈ W, lf F j w.1 * lf F k w.2 - lf F j w.2 * lf F k w.1 ≠ 0) := by
  classical
  -- the open set cut out by the strict inequalities
  set U : Set (Fin 3 → Fin 3 → ℝ) := {F | ∀ p ∈ S, lf F p.1 p.2.1 < lf F p.1 p.2.2} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ p ∈ S, {F : Fin 3 → Fin 3 → ℝ | lf F p.1 p.2.1 < lf F p.1 p.2.2} := by
      ext F; simp [hU]
    rw [this]
    refine isOpen_biInter_finset (fun p _ => isOpen_lt ?_ ?_)
    · exact continuousOn_univ.1 (analytic_lf p.1 p.2.1).continuousOn
    · exact continuousOn_univ.1 (analytic_lf p.1 p.2.2).continuousOn
  -- step 1: determinant
  obtain ⟨O1, hO1, hne1, hsub1, hp1⟩ := refine_open
    (fun (_ : Unit) (F : Fin 3 → Fin 3 → ℝ) => Matrix.det (Matrix.of F)) {()}
    (fun _ _ => analytic_det)
    (fun _ _ => ⟨sel id, by
      have : Matrix.of (sel id) = 1 := by
        ext a b
        simp only [sel, Matrix.of_apply, id, Matrix.one_apply]
        by_cases hab : a = b
        · subst hab; simp
        · simp [hab, Ne.symm hab]
      rw [this, Matrix.det_one]; exact one_ne_zero⟩)
    U hUo ⟨F0, hS⟩
  -- step 2: the linear forms on V
  obtain ⟨O2, hO2, hne2, hsub2, hp2⟩ := refine_open
    (fun (q : Fin 3 × (ℝ^3)) (F : Fin 3 → Fin 3 → ℝ) => lf F q.1 q.2)
    ((Finset.univ : Finset (Fin 3)) ×ˢ V)
    (fun q _ => analytic_lf q.1 q.2)
    (fun q hq => by
      have hv := hV q.2 (Finset.mem_product.1 hq).2
      obtain ⟨i, hi⟩ : ∃ i, q.2 i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (by ext i; simp [h i])
      exact ⟨sel (fun _ => i), by rw [lf_sel]; exact hi⟩)
    O1 hO1 hne1
  -- step 3: the 2x2 minors on W
  obtain ⟨O3, _, hne3, hsub3, hp3⟩ := refine_open
    (fun (q : (Fin 3 × Fin 3) × ((ℝ^3) × (ℝ^3))) (F : Fin 3 → Fin 3 → ℝ) =>
      lf F q.1.1 q.2.1 * lf F q.1.2 q.2.2 - lf F q.1.1 q.2.2 * lf F q.1.2 q.2.1)
    ((Finset.univ : Finset (Fin 3)).offDiag ×ˢ W)
    (fun q _ => analytic_minor q.1.1 q.1.2 q.2)
    (fun q hq => by
      obtain ⟨hjk, hw⟩ := Finset.mem_product.1 hq
      have hne : q.1.1 ≠ q.1.2 := (Finset.mem_offDiag.1 hjk).2.2
      obtain ⟨i, i', hii⟩ := exists_minor_ne q.2 (hW q.2 hw)
      refine ⟨sel (fun m => if m = q.1.1 then i else i'), ?_⟩
      simp only [lf_sel, if_pos rfl, if_neg (Ne.symm hne)]
      exact hii)
    O2 hO2 hne2
  obtain ⟨F, hF⟩ := hne3
  have hF2 := hsub3 hF
  have hF1 := hsub2 hF2
  have hFU := hsub1 hF1
  refine ⟨F, hFU, hp1 F hF1 () (Finset.mem_singleton_self _), ?_, ?_⟩
  · intro k v hv
    exact hp2 F hF2 (k, v) (Finset.mem_product.2 ⟨Finset.mem_univ _, hv⟩)
  · intro j k hjk w hw
    exact hp3 F hF ((j, k), w)
      (Finset.mem_product.2 ⟨Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩, hw⟩)


/-! ## Section 16: the triple lemma (Propositions 3.1 and 2.3 for one triple) -/

def lfLin (F : Fin 3 → Fin 3 → ℝ) (k : Fin 3) : (ℝ^3) →ₗ[ℝ] ℝ where
  toFun x := lf F k x
  map_add' x y := by simp only [lf, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [lf, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma lin_eq_lf (g : (ℝ^3) →ₗ[ℝ] ℝ) (x : ℝ^3) :
    g x = ∑ i, g (EuclideanSpace.single i (1 : ℝ)) * x i := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [EuclideanSpace.single_apply, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma exists_thresholds (g : ℝ^3 → ℝ) (A B : Finset (ℝ^3)) (h : ∀ u ∈ A, ∀ v ∈ B, g u < g v) :
    ∃ L R : ℝ, L < R ∧ (∀ u ∈ A, g u ≤ L) ∧ (∀ v ∈ B, R ≤ g v) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨0, 1, one_pos, by simp, by simp⟩
    · exact ⟨B.inf' hB g - 1, B.inf' hB g, by linarith, by simp,
        fun v hv => Finset.inf'_le _ hv⟩
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact ⟨A.sup' hA g, A.sup' hA g + 1, by linarith, fun u hu => Finset.le_sup' _ hu, by simp⟩
  refine ⟨A.sup' hA g, B.inf' hB g, ?_, fun u hu => Finset.le_sup' _ hu,
    fun v hv => Finset.inf'_le _ hv⟩
  obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup' hA g
  obtain ⟨v, hv, hv'⟩ := Finset.exists_mem_eq_inf' hB g
  rw [hu', hv']; exact h u hu v hv

lemma gp_indep {X : Finset (ℝ^3)} (hX : Erdos651.IsInGeneralPosition X) {x y z : ℝ^3}
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a b : ℝ) (hab : a • (y - x) + b • (z - x) = 0) : a = 0 ∧ b = 0 := by
  classical
  let Y : Finset (ℝ^3) := {x, y, z}
  have hYX : Y ⊆ X := by
    intro w hw; simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hYcard : Y.card ≤ 3 + 1 := by
    calc Y.card ≤ ({y, z} : Finset (ℝ^3)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
      _ ≤ 4 := by omega
  have hind := hX Y hYX hYcard
  have hxY : x ∈ Y := by simp [Y]
  have hyY : y ∈ Y := by simp [Y]
  have hzY : z ∈ Y := by simp [Y]
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥(Y : Set (ℝ^3)) → ℝ^3)
    ⟨x, hxY⟩).mp hind
  let iy : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨x, hxY⟩} :=
    ⟨⟨y, hyY⟩, fun h => hxy (congrArg Subtype.val h).symm⟩
  let iz : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨x, hxY⟩} :=
    ⟨⟨z, hzY⟩, fun h => hxz (congrArg Subtype.val h).symm⟩
  have hyz' : iy ≠ iz := fun h => hyz (congrArg (fun w => w.val.val) h)
  let coef : {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨x, hxY⟩} → ℝ :=
    fun i => if i = iy then a else if i = iz then b else 0
  have hsum : ∑ i, coef i • (i.val.val -ᵥ x) = 0 := by
    have huniv : (Finset.univ : Finset {i : ↥(Y : Set (ℝ^3)) // i ≠ ⟨x, hxY⟩}) = {iy, iz} := by
      ext i; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hiY : i.val.val ∈ Y := Finset.mem_coe.mp i.val.prop
      simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hiY
      rcases hiY with h | h | h
      · exact (i.prop (Subtype.ext h)).elim
      · left; exact Subtype.ext (Subtype.ext h)
      · right; exact Subtype.ext (Subtype.ext h)
    rw [huniv, Finset.sum_pair hyz']
    simp only [coef, ite_true, hyz'.symm, ite_false, vsub_eq_sub]
    exact hab
  have h1 := Fintype.linearIndependent_iff.mp hlin coef hsum iy
  have h2 := Fintype.linearIndependent_iff.mp hlin coef hsum iz
  simp only [coef, ite_true, hyz'.symm, ite_false] at h1 h2
  exact ⟨h1, h2⟩

lemma halfspace_convex (h : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ) (γ : Fin 3 → ℝ) :
    Convex ℝ {x : ℝ^3 | ∀ k, γ k ≤ h k x} := by
  intro x hx y hy a b ha hb hab k
  have e : h k (a • x + b • y) = a * h k x + b * h k y := by simp [map_add, map_smul]
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left (hx k) ha
  have h2 := mul_le_mul_of_nonneg_left (hy k) hb
  have h3 : γ k = a * γ k + b * γ k := by rw [← add_mul, hab, one_mul]
  linarith

theorem triple_lemma {K : ℕ} {Zs : Fin K → Finset (ℝ^3)} (h : ClusterHyp K Zs)
    {X0 : Finset (ℝ^3)} (hX0 : Erdos651.IsInGeneralPosition X0) (hsub : ∀ m, Zs m ⊆ X0)
    (j1 j2 j3 : Fin K) (h12 : j1 < j2) (h23 : j2 < j3) (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbig : (Nat.choose (a + b - 4) (a - 2)) ^ 3 * (Nat.choose (a + b - 4) (a - 2)) ^ 3
      < (Zs j2).card) :
    (∃ P : Set (ℝ^3), Convex ℝ P ∧
      (∀ m : Fin K, (m < j1 ∨ (j2 < m ∧ m ≤ j3)) → ((Zs m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P) ∧
      ((∃ Kc ⊆ Zs j2, Kc.card = a ∧ IsCCap P Kc) ∨ Erdos651.HasConvexSubset b (Zs j2))) ∨
    (∃ P : Set (ℝ^3), Convex ℝ P ∧
      (∀ m : Fin K, ((j1 ≤ m ∧ m < j2) ∨ j3 < m) → ((Zs m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P) ∧
      ((∃ Kc ⊆ Zs j2, Kc.card = a ∧ IsCCap P Kc) ∨ Erdos651.HasConvexSubset b (Zs j2))) := by
  classical
  have hZgp : Erdos651.IsInGeneralPosition (Zs j2) :=
    fun Y hY hc => hX0 Y (hY.trans (hsub j2)) hc
  -- the three separations
  obtain ⟨φ0, c0, hφa, hφb⟩ := h.vsep j2
  set others := (Finset.univ.filter (fun m : Fin K => m ≠ j2)).biUnion Zs with hothers
  set U13a := arcUnion Zs true j1.val (j2.val + 1) (j3.val + 1)
  set U24a := arcUnion Zs false j1.val (j2.val + 1) (j3.val + 1)
  set U13b := arcUnion Zs true j1.val j2.val (j3.val + 1)
  set U24b := arcUnion Zs false j1.val j2.val (j3.val + 1)
  have h12' : j1.val < j2.val := h12
  have h23' : j2.val < j3.val := h23
  obtain ⟨f1, c1, hf1a, hf1b⟩ := strict_sep_convexHull_finset U13a U24a
    (cluster_arcs_disjoint h _ _ _ (by omega) (by omega))
  obtain ⟨f2, c2, hf2a, hf2b⟩ := strict_sep_convexHull_finset U13b U24b
    (cluster_arcs_disjoint h _ _ _ (by omega) (by omega))
  have memArc : ∀ (odd : Bool) (a' b' c' : ℕ) (m : Fin K), (OddArc a' b' c' m.val ↔ odd = true) →
      Zs m ⊆ arcUnion Zs odd a' b' c' := by
    intro odd a' b' c' m hm x hx
    exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hx⟩
  have memOthers : ∀ m, m ≠ j2 → Zs m ⊆ others := fun m hm x hx =>
    Finset.mem_biUnion.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hx⟩
  -- the matrix of the three functionals
  let row : ((ℝ^3) →ₗ[ℝ] ℝ) → Fin 3 → ℝ := fun g i => g (EuclideanSpace.single i (1 : ℝ))
  let F0 : Fin 3 → Fin 3 → ℝ := ![row φ0, row f1, row f2]
  have hF0 : ∀ x, lf F0 0 x = φ0 x ∧ lf F0 1 x = f1 x ∧ lf F0 2 x = f2 x := by
    intro x
    refine ⟨?_, ?_, ?_⟩ <;> simp only [lf, F0, row] <;> rw [lin_eq_lf] <;> simp
  let S : Finset (Fin 3 × (ℝ^3) × (ℝ^3)) :=
    ((Zs j2 ×ˢ others).image (fun pr => ((0 : Fin 3), pr.1, pr.2))) ∪
    ((U24a ×ˢ U13a).image (fun pr => ((1 : Fin 3), pr.1, pr.2))) ∪
    ((U24b ×ˢ U13b).image (fun pr => ((2 : Fin 3), pr.1, pr.2)))
  have hS : ∀ p ∈ S, lf F0 p.1 p.2.1 < lf F0 p.1 p.2.2 := by
    intro p hp
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hp
    rcases hp with (⟨pr, ⟨h1, h2⟩, rfl⟩ | ⟨pr, ⟨h1, h2⟩, rfl⟩) | ⟨pr, ⟨h1, h2⟩, rfl⟩
    · rw [(hF0 _).1, (hF0 _).1]
      obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp h2
      have := hφa _ h1
      have := hφb m (Finset.mem_filter.mp hm).2 _ hxm
      linarith
    · rw [(hF0 _).2.1, (hF0 _).2.1]
      have := hf1a _ h2; have := hf1b _ h1; linarith
    · rw [(hF0 _).2.2, (hF0 _).2.2]
      have := hf2a _ h2; have := hf2b _ h1; linarith
  let V : Finset (ℝ^3) := ((Zs j2 ×ˢ Zs j2).filter (fun pr => pr.1 ≠ pr.2)).image
    (fun pr => pr.1 - pr.2)
  have hV : ∀ v ∈ V, v ≠ 0 := by
    intro v hv
    simp only [V, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hv
    obtain ⟨pr, ⟨-, hne⟩, rfl⟩ := hv
    exact sub_ne_zero.mpr hne
  let W : Finset ((ℝ^3) × (ℝ^3)) :=
    ((Zs j2 ×ˢ Zs j2 ×ˢ Zs j2).filter
      (fun tr => tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2)).image
      (fun tr => (tr.2.1 - tr.1, tr.2.2 - tr.1))
  have hW : ∀ w ∈ W, ∀ a b : ℝ, a • w.1 + b • w.2 = 0 → a = 0 ∧ b = 0 := by
    intro w hw a' b' hab
    simp only [W, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hw
    obtain ⟨tr, ⟨⟨h1, h2, h3⟩, hn1, hn2, hn3⟩, rfl⟩ := hw
    exact gp_indep hZgp h1 h2 h3 hn1 hn2 hn3 a' b' hab
  obtain ⟨F, hFS, -, hFV, hFW⟩ := generic_choice F0 S hS V hV W hW
  let g : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ := lfLin F
  have hg : ∀ k x, g k x = lf F k x := fun _ _ => rfl
  -- separations survive
  have s0 : ∀ u ∈ Zs j2, ∀ v ∈ others, g 0 u < g 0 v := fun u hu v hv =>
    hFS (((0 : Fin 3)), u, v) (by
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_product]
      exact Or.inl (Or.inl ⟨(u, v), ⟨hu, hv⟩, rfl⟩))
  have s1 : ∀ u ∈ U24a, ∀ v ∈ U13a, g 1 u < g 1 v := fun u hu v hv =>
    hFS (((1 : Fin 3)), u, v) (by
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_product]
      exact Or.inl (Or.inr ⟨(u, v), ⟨hu, hv⟩, rfl⟩))
  have s2 : ∀ u ∈ U24b, ∀ v ∈ U13b, g 2 u < g 2 v := fun u hu v hv =>
    hFS (((2 : Fin 3)), u, v) (by
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_product]
      exact Or.inr ⟨(u, v), ⟨hu, hv⟩, rfl⟩)
  obtain ⟨L0, R0, hLR0, hL0, hR0⟩ := exists_thresholds (g 0) _ _ s0
  obtain ⟨L1, R1, hLR1, hL1, hR1⟩ := exists_thresholds (g 1) _ _ s1
  obtain ⟨L2, R2, hLR2, hL2, hR2⟩ := exists_thresholds (g 2) _ _ s2
  -- genericity on Zs j2
  have ginj : ∀ k, ∀ x ∈ Zs j2, ∀ y ∈ Zs j2, x ≠ y → g k x ≠ g k y := by
    intro k x hx y hy hxy heq
    apply hFV k (x - y) (Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩)
    rw [← hg, map_sub, heq, sub_self]
  have ggp : ∀ j k : Fin 3, j ≠ k → ∀ x ∈ Zs j2, ∀ y ∈ Zs j2, ∀ z ∈ Zs j2, x ≠ y → y ≠ z →
      x ≠ z → g j (y - x) * g k (z - x) - g j (z - x) * g k (y - x) ≠ 0 := by
    intro j k hjk x hx y hy z hz hxy hyz hxz
    exact hFW j k hjk _ (Finset.mem_image.mpr ⟨(x, y, z), Finset.mem_filter.mpr
      ⟨by simp [hx, hy, hz], hxy, hyz, hxz⟩, rfl⟩)
  -- location of the middle cluster
  have hZ0 : ∀ x ∈ Zs j2, g 0 x ≤ L0 := fun x hx => hL0 x hx
  have hZ1 : ∀ x ∈ Zs j2, g 1 x ≤ L1 := fun x hx =>
    hL1 x (memArc false _ _ _ j2 (by simp only [OddArc, Bool.false_eq_true, iff_false]; omega) hx)
  have hZ2 : ∀ x ∈ Zs j2, R2 ≤ g 2 x := fun x hx =>
    hR2 x (memArc true _ _ _ j2 (by simp only [OddArc, iff_true]; omega) hx)
  -- the two polyhedra
  let h1v : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ := ![g 0, g 1, g 2]
  let γ1 : Fin 3 → ℝ := ![R0, R1, R2]
  let h2v : Fin 3 → (ℝ^3) →ₗ[ℝ] ℝ := ![g 0, -g 1, -g 2]
  let γ2 : Fin 3 → ℝ := ![R0, -L1, -L2]
  set P1 : Set (ℝ^3) := {x | ∀ k, γ1 k ≤ h1v k x} with hP1
  set P2 : Set (ℝ^3) := {x | ∀ k, γ2 k ≤ h2v k x} with hP2
  have hP1mem : ∀ x, x ∈ P1 ↔ R0 ≤ g 0 x ∧ R1 ≤ g 1 x ∧ R2 ≤ g 2 x := by
    intro x; simp only [hP1, Set.mem_setOf_eq]
    constructor
    · intro hk; exact ⟨hk 0, hk 1, hk 2⟩
    · rintro ⟨a0, a1, a2⟩ k; fin_cases k <;> simpa [h1v, γ1]
  have hP2mem : ∀ x, x ∈ P2 ↔ R0 ≤ g 0 x ∧ g 1 x ≤ L1 ∧ g 2 x ≤ L2 := by
    intro x; simp only [hP2, Set.mem_setOf_eq]
    constructor
    · intro hk
      have a1 := hk 1; have a2 := hk 2
      simp [h2v, γ2] at a1 a2
      exact ⟨hk 0, a1, a2⟩
    · rintro ⟨a0, a1, a2⟩ k; fin_cases k <;> simp [h2v, γ2] <;> linarith
  -- containments
  have hred : ∀ m : Fin K, (m < j1 ∨ (j2 < m ∧ m ≤ j3)) → ((Zs m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P1 := by
    intro m hm x hx
    have hm' : m ≠ j2 := by rintro rfl; rcases hm with hm | hm <;> [exact absurd (hm.trans h12) (lt_irrefl _); exact lt_irrefl _ hm.1]
    have hmv : m.val < j1.val ∨ (j2.val < m.val ∧ m.val ≤ j3.val) := by
      rcases hm with hm | hm
      · left; exact hm
      · right; exact ⟨hm.1, hm.2⟩
    rw [hP1mem]
    refine ⟨hR0 x (memOthers m hm' hx), hR1 x (memArc true _ _ _ m ?_ hx),
      hR2 x (memArc true _ _ _ m ?_ hx)⟩ <;> simp only [OddArc, iff_true] <;> omega
  have hblue : ∀ m : Fin K, ((j1 ≤ m ∧ m < j2) ∨ j3 < m) → ((Zs m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P2 := by
    intro m hm x hx
    have hmv : (j1.val ≤ m.val ∧ m.val < j2.val) ∨ j3.val < m.val := by
      rcases hm with hm | hm
      · left; exact ⟨hm.1, hm.2⟩
      · right; exact hm
    have hm' : m ≠ j2 := by
      rintro rfl; rcases hmv with hm | hm <;> omega
    rw [hP2mem]
    refine ⟨hR0 x (memOthers m hm' hx), hL1 x (memArc false _ _ _ m ?_ hx),
      hL2 x (memArc false _ _ _ m ?_ hx)⟩ <;> simp only [OddArc, Bool.false_eq_true, iff_false] <;> omega
  -- the order on the middle cluster
  set B := (Nat.choose (a + b - 4) (a - 2)) ^ 3 with hB
  let Rsub : ↥(Zs j2) → ↥(Zs j2) → Prop := fun x y => precR P1 x.val y.val
  have hxP1 : ∀ x ∈ Zs j2, x ∉ P1 := fun x hx hP => by
    have := ((hP1mem x).mp hP).1; have := hZ0 x hx; linarith
  have hP1conv : Convex ℝ P1 := halfspace_convex h1v γ1
  rcases mirsky_chain_or_antichain (R := Rsub) (fun x => precR_refl _ _)
      (fun x y z hxy hyz => precR_trans hP1conv hxy hyz)
      (fun x y hxy hyx => Subtype.ext (precR_antisymm hP1conv (hxP1 x.val x.prop) hxy hyx))
      Finset.univ B B (by rw [Finset.card_univ, Fintype.card_coe]; exact hbig)
    with ⟨C, -, hCch, hCcard⟩ | ⟨A, -, hAan, hAcard⟩
  · -- chain: blue
    right
    refine ⟨P2, halfspace_convex h2v γ2, hblue, ?_⟩
    set Z := C.image Subtype.val
    have hZsub : Z ⊆ Zs j2 := by
      intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.prop
    have hZcard : Z.card = C.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hfree : IsCFree P2 Z := by
      refine free_of_chain (P := P1) (g 0) ((L0 + R0) / 2) ?_ ?_ ?_ (g 1) ((L1 + R1) / 2) ?_ ?_ ?_
        (-g 2) (-((L2 + R2) / 2)) ?_ ?_ ?_ ?_
      · intro x hx; have := hZ0 x (hZsub hx); linarith
      · intro p hp; have := ((hP1mem p).mp hp).1; linarith
      · intro q hq; have := ((hP2mem q).mp hq).1; linarith
      · intro p hp; have := ((hP1mem p).mp hp).2.1; linarith
      · intro x hx; have := hZ1 x (hZsub hx); linarith
      · intro q hq; have := ((hP2mem q).mp hq).2.1; linarith
      · intro q hq; have := ((hP2mem q).mp hq).2.2; simp only [LinearMap.neg_apply]; linarith
      · intro x hx; have := hZ2 x (hZsub hx); simp only [LinearMap.neg_apply]; linarith
      · intro p hp; have := ((hP1mem p).mp hp).2.2; simp only [LinearMap.neg_apply]; linarith
      · intro x hx y hy
        obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        exact hCch x' hx' y' hy'
    let σ : Fin 3 → ℝ := ![1, -1, -1]
    have hσ : ∀ k u, h2v k u = σ k * g k u := by intro k u; fin_cases k <;> simp [h2v, σ]
    have hσne : ∀ k, σ k ≠ 0 := by intro k; fin_cases k <;> simp [σ]
    have h2inj : ∀ k, ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → h2v k x ≠ h2v k y := by
      intro k x hx y hy hxy heq
      rw [hσ, hσ] at heq
      exact ginj k x (hZsub hx) y (hZsub hy) hxy (mul_left_cancel₀ (hσne k) heq)
    have h2gp : ∀ j k : Fin 3, j ≠ k → ∀ x ∈ Z, ∀ y ∈ Z, ∀ z ∈ Z, x ≠ y → y ≠ z → x ≠ z →
        h2v j (y - x) * h2v k (z - x) - h2v j (z - x) * h2v k (y - x) ≠ 0 := by
      intro j k hjk x hx y hy z hz hxy hyz hxz h0
      have hm := ggp j k hjk x (hZsub hx) y (hZsub hy) z (hZsub hz) hxy hyz hxz
      rw [hσ, hσ, hσ, hσ] at h0
      have e : σ j * g j (y - x) * (σ k * g k (z - x)) - σ j * g j (z - x) * (σ k * g k (y - x)) =
          (σ j * σ k) * (g j (y - x) * g k (z - x) - g j (z - x) * g k (y - x)) := by ring
      rw [e] at h0
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact mul_ne_zero (hσne j) (hσne k) h'
      · exact hm h'
    have hsign : ∀ x ∈ Z, h2v 0 x < γ2 0 ∧ (h2v 1 x < γ2 1 ∨ h2v 2 x < γ2 2) := by
      intro x hx
      have := hZ0 x (hZsub hx); have := hZ2 x (hZsub hx)
      refine ⟨by simp [h2v, γ2]; linarith, Or.inr ?_⟩
      simp [h2v, γ2]; linarith
    rcases halfspace_cups_caps Z h2v γ2 h2inj h2gp hsign hfree a b ha hb (by rw [hZcard]; exact hCcard)
      with ⟨Kc, hKc, hKcard, hcap⟩ | hconv
    · exact Or.inl ⟨Kc, hKc.trans hZsub, hKcard, hcap⟩
    · obtain ⟨Wc, hW1, hW2, hW3⟩ := hconv
      exact Or.inr ⟨Wc, hW1.trans hZsub, hW2, hW3⟩
  · -- antichain: red
    left
    refine ⟨P1, hP1conv, hred, ?_⟩
    set Z := A.image Subtype.val
    have hZsub : Z ⊆ Zs j2 := by
      intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.prop
    have hZcard : Z.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hfree : IsCFree P1 Z := by
      refine free_of_antichain (g 0) R0 ?_ ?_ ?_
      · intro x hx; have := hZ0 x (hZsub hx); linarith
      · intro p hp; exact ((hP1mem p).mp hp).1
      · intro x hx y hy hxy hpre
        obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        exact hAan x' hx' y' hy' (fun e => hxy (by rw [e])) hpre
    have h1inj : ∀ k, ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → h1v k x ≠ h1v k y := by
      intro k x hx y hy hxy
      fin_cases k <;> simpa [h1v] using ginj _ x (hZsub hx) y (hZsub hy) hxy
    have h1gp : ∀ j k : Fin 3, j ≠ k → ∀ x ∈ Z, ∀ y ∈ Z, ∀ z ∈ Z, x ≠ y → y ≠ z → x ≠ z →
        h1v j (y - x) * h1v k (z - x) - h1v j (z - x) * h1v k (y - x) ≠ 0 := by
      intro j k hjk x hx y hy z hz hxy hyz hxz
      have hm := ggp j k hjk x (hZsub hx) y (hZsub hy) z (hZsub hz) hxy hyz hxz
      have hσ1 : ∀ k u, h1v k u = g k u := by intro k u; fin_cases k <;> simp [h1v]
      rw [hσ1, hσ1, hσ1, hσ1]; exact hm
    have hsign : ∀ x ∈ Z, h1v 0 x < γ1 0 ∧ (h1v 1 x < γ1 1 ∨ h1v 2 x < γ1 2) := by
      intro x hx
      have := hZ0 x (hZsub hx); have := hZ1 x (hZsub hx)
      refine ⟨by simp [h1v, γ1]; linarith, Or.inl ?_⟩
      simp [h1v, γ1]; linarith
    rcases halfspace_cups_caps Z h1v γ1 h1inj h1gp hsign hfree a b ha hb (by rw [hZcard]; exact hAcard)
      with ⟨Kc, hKc, hKcard, hcap⟩ | hconv
    · exact Or.inl ⟨Kc, hKc.trans hZsub, hKcard, hcap⟩
    · obtain ⟨Wc, hW1, hW2, hW3⟩ := hconv
      exact Or.inr ⟨Wc, hW1.trans hZsub, hW2, hW3⟩

/-! ## Section 17: Ramsey on triples and the final convex polytope -/

lemma sorted_triple_unique {j1 j2 j3 k1 k2 k3 : ℕ} (hj : j1 < j2 ∧ j2 < j3) (hk : k1 < k2 ∧ k2 < k3)
    (h : ({j1, j2, j3} : Finset ℕ) = {k1, k2, k3}) : j1 = k1 ∧ j2 = k2 ∧ j3 = k3 := by
  have m1 : j1 ∈ ({k1, k2, k3} : Finset ℕ) := by rw [← h]; simp
  have m2 : j2 ∈ ({k1, k2, k3} : Finset ℕ) := by rw [← h]; simp
  have m3 : j3 ∈ ({k1, k2, k3} : Finset ℕ) := by rw [← h]; simp
  have n1 : k1 ∈ ({j1, j2, j3} : Finset ℕ) := by rw [h]; simp
  have n2 : k2 ∈ ({j1, j2, j3} : Finset ℕ) := by rw [h]; simp
  have n3 : k3 ∈ ({j1, j2, j3} : Finset ℕ) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 n1 n2 n3
  omega

lemma card_three {i j k : ℕ} (h1 : i < j) (h2 : j < k) : ({i, j, k} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_pair (by omega)]
  simp only [Finset.mem_insert, Finset.mem_singleton]; omega

theorem cluster_bound (t : ℕ) (ht : 1 ≤ t) (N3 : ℕ)
    (hN3 : ∀ S : Finset ℕ, N3 ≤ S.card → ∀ c : Finset ℕ → Bool,
      (∃ T ⊆ S, T.card = 2 * t + 2 ∧ ∀ e ⊆ T, e.card = 3 → c e = true) ∨
      (∃ T ⊆ S, T.card = 2 * t + 2 ∧ ∀ e ⊆ T, e.card = 3 → c e = false))
    {K : ℕ} (hK : N3 ≤ K) {Zs : Fin K → Finset (ℝ^3)} (h : ClusterHyp K Zs)
    {X0 : Finset (ℝ^3)} (hX0 : Erdos651.IsInGeneralPosition X0) (hsub : ∀ m, Zs m ⊆ X0)
    (n a : ℕ) (ha : 2 ≤ a) (hn : 2 ≤ n) (hta : n ≤ t * a)
    (hnot : ¬ Erdos651.HasConvexSubset n X0) :
    ∃ m, (Zs m).card ≤
      (Nat.choose (a + n - 4) (a - 2)) ^ 3 * (Nat.choose (a + n - 4) (a - 2)) ^ 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  let Red : Fin K → Fin K → Fin K → Prop := fun j1 j2 j3 =>
    ∃ P : Set (ℝ^3), Convex ℝ P ∧
      (∀ m : Fin K, (m < j1 ∨ (j2 < m ∧ m ≤ j3)) → ((Zs m : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P) ∧
      ((∃ Kc ⊆ Zs j2, Kc.card = a ∧ IsCCap P Kc) ∨ Erdos651.HasConvexSubset n (Zs j2))
  let col : Finset ℕ → Bool := fun e =>
    decide (∀ j1 j2 j3 : Fin K, j1 < j2 → j2 < j3 → e = {j1.val, j2.val, j3.val} → Red j1 j2 j3)
  have hrange : N3 ≤ (Finset.range K).card := by rw [Finset.card_range]; exact hK
  -- positions in a monochromatic set
  have hconv_sub : ∀ m, ¬ Erdos651.HasConvexSubset n (Zs m) := fun m hc => by
    obtain ⟨W, hW1, hW2, hW3⟩ := hc
    exact hnot ⟨W, hW1.trans (hsub m), hW2, hW3⟩
  -- the common finishing argument
  have finish : ∀ (idx : Fin t → Fin K), Function.Injective idx →
      (∀ r : Fin t, ∃ P : Set (ℝ^3), ∃ Kc : Finset (ℝ^3), Kc ⊆ Zs (idx r) ∧ Kc.card = a ∧
        IsCCap P Kc ∧ ∀ r' : Fin t, r' ≠ r → ((Zs (idx r') : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P) →
      False := by
    intro idx hidx hall
    choose P Kc hKsub hKcard hKcap hKin using hall
    have hconvU := union_caps_convex Finset.univ Kc P (fun r _ => hKcap r)
      (fun r _ r' _ hne => (Set.Subset.trans (by exact_mod_cast hKsub r') (hKin r r' hne)))
    have hdisj : ∀ r ∈ (Finset.univ : Finset (Fin t)), ∀ r' ∈ (Finset.univ : Finset (Fin t)),
        r ≠ r' → Disjoint (Kc r) (Kc r') := by
      intro r _ r' _ hne
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact h.disj (fun e => hne (hidx e)) (hKsub r hx) (hKsub r' hx')
    have hcard : (Finset.univ.biUnion Kc).card = t * a := by
      rw [Finset.card_biUnion hdisj]
      simp [hKcard]
    apply hnot
    refine hasConvexSubset_of_convex ?_ (by rw [hcard]; exact hta) hconvU
    intro x hx
    obtain ⟨r, -, hxr⟩ := Finset.mem_biUnion.mp hx
    exact hsub _ (hKsub r hxr)
  rcases hN3 (Finset.range K) hrange col with ⟨T, hTS, hTcard, hTcol⟩ | ⟨T, hTS, hTcard, hTcol⟩
  all_goals
    let emb := T.orderEmbOfFin hTcard
    have hembK : ∀ i, emb i < K := fun i => Finset.mem_range.mp (hTS (T.orderEmbOfFin_mem hTcard i))
    let pos : Fin (2 * t + 2) → Fin K := fun i => ⟨emb i, hembK i⟩
    have hpos_lt : ∀ i j, i < j → pos i < pos j := fun i j hij => by
      show emb i < emb j; exact emb.strictMono hij
    have hpos_le : ∀ i j, i ≤ j → pos i ≤ pos j := fun i j hij => by
      show emb i ≤ emb j; exact emb.monotone hij
    have hsubT : ∀ i j k : Fin (2 * t + 2), i < j → j < k →
        ({(pos i).val, (pos j).val, (pos k).val} : Finset ℕ) ⊆ T := by
      intro i j k _ _ x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact T.orderEmbOfFin_mem hTcard _
    have hcard3 : ∀ i j k : Fin (2 * t + 2), i < j → j < k →
        ({(pos i).val, (pos j).val, (pos k).val} : Finset ℕ).card = 3 := fun i j k hij hjk =>
      card_three (hpos_lt i j hij) (hpos_lt j k hjk)
  · -- red: triples (pos (2r), pos (2r+1), pos (2t+1))
    let idx : Fin t → Fin K := fun r => pos ⟨2 * r.val + 1, by omega⟩
    apply finish idx
    · intro r r' he
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
      · exact (ne_of_lt (hpos_lt _ _ (by simp only [Fin.lt_def]; omega))) he
      · exact (ne_of_gt (hpos_lt _ _ (by simp only [Fin.lt_def]; omega))) he
    intro r
    let i0 : Fin (2 * t + 2) := ⟨2 * r.val, by omega⟩
    let i1 : Fin (2 * t + 2) := ⟨2 * r.val + 1, by omega⟩
    let i2 : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
    have h01 : i0 < i1 := by simp only [Fin.lt_def, i0, i1]; omega
    have h12 : i1 < i2 := by simp only [Fin.lt_def, i1, i2]; omega
    have hc := hTcol _ (hsubT i0 i1 i2 h01 h12) (hcard3 i0 i1 i2 h01 h12)
    have hred : Red (pos i0) (pos i1) (pos i2) := by
      simp only [col, decide_eq_true_eq] at hc
      exact hc _ _ _ (hpos_lt _ _ h01) (hpos_lt _ _ h12) rfl
    obtain ⟨P, -, hPin, hcap | hcv⟩ := hred
    · obtain ⟨Kc, hKc, hKcard, hKcap⟩ := hcap
      refine ⟨P, Kc, hKc, hKcard, hKcap, fun r' hne => hPin _ ?_⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
      · left; exact hpos_lt _ _ (by simp only [Fin.lt_def, i0]; omega)
      · right; exact ⟨hpos_lt _ _ (by simp only [Fin.lt_def, i1]; omega),
          hpos_le _ _ (by simp only [Fin.le_def, i2]; omega)⟩
    · exact absurd hcv (hconv_sub _)
  · -- blue: triples (pos 0, pos (2r+1), pos (2r+2))
    let idx : Fin t → Fin K := fun r => pos ⟨2 * r.val + 1, by omega⟩
    apply finish idx
    · intro r r' he
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
      · exact (ne_of_lt (hpos_lt _ _ (by simp only [Fin.lt_def]; omega))) he
      · exact (ne_of_gt (hpos_lt _ _ (by simp only [Fin.lt_def]; omega))) he
    intro r
    let i0 : Fin (2 * t + 2) := ⟨0, by omega⟩
    let i1 : Fin (2 * t + 2) := ⟨2 * r.val + 1, by omega⟩
    let i2 : Fin (2 * t + 2) := ⟨2 * r.val + 2, by omega⟩
    have h01 : i0 < i1 := by simp only [Fin.lt_def, i0, i1]; omega
    have h12 : i1 < i2 := by simp only [Fin.lt_def, i1, i2]; omega
    have hc := hTcol _ (hsubT i0 i1 i2 h01 h12) (hcard3 i0 i1 i2 h01 h12)
    have hnred : ¬ Red (pos i0) (pos i1) (pos i2) := by
      intro hr
      simp only [col, decide_eq_false_iff_not] at hc
      apply hc
      intro j1 j2 j3 hj12 hj23 he
      have hu := sorted_triple_unique ⟨hpos_lt _ _ h01, hpos_lt _ _ h12⟩
        ⟨(show j1.val < j2.val from hj12), (show j2.val < j3.val from hj23)⟩ he
      have e1 : j1 = pos i0 := Fin.ext hu.1.symm
      have e2 : j2 = pos i1 := Fin.ext hu.2.1.symm
      have e3 : j3 = pos i2 := Fin.ext hu.2.2.symm
      rw [e1, e2, e3]; exact hr
    rcases triple_lemma h hX0 hsub (pos i0) (pos i1) (pos i2) (hpos_lt _ _ h01) (hpos_lt _ _ h12)
      a n ha hn (hcon _) with hr | ⟨P, -, hPin, hcap | hcv⟩
    · exact absurd hr hnred
    · obtain ⟨Kc, hKc, hKcard, hKcap⟩ := hcap
      refine ⟨P, Kc, hKc, hKcard, hKcap, fun r' hne => hPin _ ?_⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
      · left; exact ⟨hpos_le _ _ (by simp only [Fin.le_def, i0]; omega),
          hpos_lt _ _ (by simp only [Fin.lt_def, i1]; omega)⟩
      · right; exact hpos_lt _ _ (by simp only [Fin.lt_def, i2]; omega)
    · exact absurd hcv (hconv_sub _)

/-! ## Section 18: from point sets to clusters, and the main theorem -/

/-- Reflection in the horizontal plane. -/
def reflZ : (ℝ^3) ≃ₗ[ℝ] (ℝ^3) where
  toFun x := !₂[x 0, x 1, -x 2]
  invFun x := !₂[x 0, x 1, -x 2]
  left_inv x := by ext k; fin_cases k <;> simp
  right_inv x := by ext k; fin_cases k <;> simp
  map_add' x y := by ext k; fin_cases k <;> simp; ring
  map_smul' r x := by ext k; fin_cases k <;> simp

lemma projXY_reflZ (x : ℝ^3) : projXY (reflZ x) = projXY x := by
  ext k; fin_cases k <;> simp [projXY, reflZ]

lemma vol_reflZ (a b c d : ℝ^3) : vol (reflZ a) (reflZ b) (reflZ c) (reflZ d) = - vol a b c d := by
  simp [vol, reflZ]; ring

lemma disjoint_hull_image (T : (ℝ^3) ≃ₗ[ℝ] (ℝ^3)) (A B : Finset (ℝ^3))
    (h : Disjoint (convexHull ℝ (A : Set (ℝ^3))) (convexHull ℝ (B : Set (ℝ^3)))) :
    Disjoint (convexHull ℝ ((A.image T : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ ((B.image T : Finset (ℝ^3)) : Set (ℝ^3))) := by
  classical
  have e : ∀ S : Finset (ℝ^3), convexHull ℝ ((S.image T : Finset (ℝ^3)) : Set (ℝ^3)) =
      T '' convexHull ℝ (S : Set (ℝ^3)) := by
    intro S
    have := T.toLinearMap.image_convexHull (S : Set (ℝ^3))
    simp only [LinearEquiv.coe_coe] at this
    rw [this, Finset.coe_image]
  rw [e, e]
  exact (Set.disjoint_image_iff T.injective).mpr h

/-- Base hypotheses on clusters (everything but the above/below pattern). -/
structure ClusterBase (K : ℕ) (Xs : Fin K → Finset (ℝ^3)) : Prop where
  vsep : ∀ i, ∃ (φ : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ x ∈ Xs i, φ x < c) ∧ (∀ j, j ≠ i → ∀ x ∈ Xs j, c < φ x)
  sep2 : Is2Separated K Xs
  ccw : ∀ a b d : Fin K, a < b → b < d → ∀ x ∈ Xs a, ∀ y ∈ Xs b, ∀ z ∈ Xs d,
    0 < orient2 (projXY x) (projXY y) (projXY z)

lemma ClusterBase.quad {K : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterBase K Xs)
    {i i' j j' : Fin K} (h1 : i < i') (h2 : i' < j) (h3 : j < j') :
    QuadHyp (Xs i) (Xs i') (Xs j) (Xs j') := by
  refine ⟨fun a ha c hc b hb d hd => ⟨h.ccw _ _ _ h1 h2 a ha c hc b hb,
    h.ccw _ _ _ (h1.trans h2) h3 a ha b hb d hd, h.ccw _ _ _ h2 h3 c hc b hb d hd,
    h.ccw _ _ _ h1 (h2.trans h3) a ha c hc d hd⟩, ?_⟩
  exact h.sep2 i j i' j' (ne_of_lt h1) (ne_of_lt (h1.trans (h2.trans h3))) (ne_of_gt h2)
    (ne_of_lt h3)

lemma ClusterBase.comp {K L : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterBase K Xs)
    (e : Fin L ↪o Fin K) : ClusterBase L (fun m => Xs (e m)) := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · obtain ⟨φ, c, h1, h2⟩ := h.vsep (e i)
    exact ⟨φ, c, h1, fun j hj x hx => h2 (e j) (fun he => hj (e.injective he)) x hx⟩
  · intro i j i' j' h1 h2 h3 h4
    exact h.sep2 (e i) (e j) (e i') (e j') (fun he => h1 (e.injective he))
      (fun he => h2 (e.injective he)) (fun he => h3 (e.injective he)) (fun he => h4 (e.injective he))
  · intro a b d hab hbd x hx y hy z hz
    exact h.ccw _ _ _ (e.strictMono hab) (e.strictMono hbd) x hx y hy z hz

lemma ClusterBase.reflect {K : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterBase K Xs) :
    ClusterBase K (fun m => (Xs m).image reflZ) := by
  classical
  refine ⟨fun i => ?_, ?_, ?_⟩
  · obtain ⟨φ, c, h1, h2⟩ := h.vsep i
    have hinv : ∀ y, reflZ (reflZ y) = y := fun y => by ext k; fin_cases k <;> simp [reflZ]
    refine ⟨φ.comp reflZ.toLinearMap, c, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      show φ (reflZ (reflZ y)) < c
      rw [hinv]; exact h1 y hy
    · intro j hj x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      show c < φ (reflZ (reflZ y))
      rw [hinv]; exact h2 j hj y hy
  · intro i j i' j' h1 h2 h3 h4
    have := disjoint_hull_image reflZ _ _ (h.sep2 i j i' j' h1 h2 h3 h4)
    simpa [Finset.image_union] using this
  · intro a b d hab hbd x hx y hy z hz
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    rw [projXY_reflZ, projXY_reflZ, projXY_reflZ]
    exact h.ccw a b d hab hbd x' hx' y' hy' z' hz'

lemma ClusterBase.toHyp {K : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterBase K Xs)
    (habove : ∀ i i' j j' : Fin K, i < i' → i' < j → j < j' →
      ∀ x ∈ Xs i, ∀ x' ∈ Xs i', ∀ y ∈ Xs j, ∀ y' ∈ Xs j', 0 < vol x y x' y') :
    ClusterHyp K Xs := ⟨h.vsep, h.sep2, h.ccw, habove⟩

lemma ClusterBase.toHyp_reflect {K : ℕ} {Xs : Fin K → Finset (ℝ^3)} (h : ClusterBase K Xs)
    (hbelow : ∀ i i' j j' : Fin K, i < i' → i' < j → j < j' →
      ∀ x ∈ Xs i, ∀ x' ∈ Xs i', ∀ y ∈ Xs j, ∀ y' ∈ Xs j', vol x y x' y' < 0) :
    ClusterHyp K (fun m => (Xs m).image reflZ) := by
  refine h.reflect.toHyp ?_
  intro i i' j j' h1 h2 h3 x hx x' hx' y hy y' hy'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy'
  rw [vol_reflZ]
  have := hbelow i i' j j' h1 h2 h3 a ha b hb c hc d hd
  linarith

/-- Ramsey on quadruples of clusters: a large subfamily satisfies `ClusterHyp`, possibly after
reflecting. -/
theorem ramsey_quadruples (K K0 N4 : ℕ)
    (hN4 : ∀ S : Finset ℕ, N4 ≤ S.card → ∀ c : Finset ℕ → Bool,
      (∃ T ⊆ S, T.card = K ∧ ∀ e ⊆ T, e.card = 4 → c e = true) ∨
      (∃ T ⊆ S, T.card = K ∧ ∀ e ⊆ T, e.card = 4 → c e = false))
    (hK0 : N4 ≤ K0) {Xs : Fin K0 → Finset (ℝ^3)} (h : ClusterBase K0 Xs)
    (hne : ∀ i, (Xs i).Nonempty) :
    ∃ e : Fin K ↪o Fin K0,
      ClusterHyp K (fun m => Xs (e m)) ∨ ClusterHyp K (fun m => (Xs (e m)).image reflZ) := by
  classical
  let r : Fin K0 → ℝ^3 := fun i => (hne i).choose
  have hr : ∀ i, r i ∈ Xs i := fun i => (hne i).choose_spec
  let col : Finset ℕ → Bool := fun e => decide (∀ i i' j j' : Fin K0, i < i' → i' < j → j < j' →
    e = {i.val, i'.val, j.val, j'.val} → 0 < vol (r i) (r j) (r i') (r j'))
  have hcard4 : ∀ i i' j j' : Fin K0, i < i' → i' < j → j < j' →
      ({i.val, i'.val, j.val, j'.val} : Finset ℕ).card = 4 := by
    intro i i' j j' h1 h2 h3
    have h1' : i.val < i'.val := h1
    have h2' : i'.val < j.val := h2
    have h3' : j.val < j'.val := h3
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (by omega)]
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have huniq : ∀ i i' j j' k k' l l' : Fin K0, i < i' → i' < j → j < j' → k < k' → k' < l → l < l' →
      ({i.val, i'.val, j.val, j'.val} : Finset ℕ) = {k.val, k'.val, l.val, l'.val} →
      i = k ∧ i' = k' ∧ j = l ∧ j' = l' := by
    intro i i' j j' k k' l l' h1 h2 h3 h4 h5 h6 he
    have h1' : i.val < i'.val := h1
    have h2' : i'.val < j.val := h2
    have h3' : j.val < j'.val := h3
    have h4' : k.val < k'.val := h4
    have h5' : k'.val < l.val := h5
    have h6' : l.val < l'.val := h6
    have m1 : i.val ∈ ({k.val, k'.val, l.val, l'.val} : Finset ℕ) := by rw [← he]; simp
    have m2 : i'.val ∈ ({k.val, k'.val, l.val, l'.val} : Finset ℕ) := by rw [← he]; simp
    have m3 : j.val ∈ ({k.val, k'.val, l.val, l'.val} : Finset ℕ) := by rw [← he]; simp
    have m4 : j'.val ∈ ({k.val, k'.val, l.val, l'.val} : Finset ℕ) := by rw [← he]; simp
    have n1 : k.val ∈ ({i.val, i'.val, j.val, j'.val} : Finset ℕ) := by rw [he]; simp
    have n2 : k'.val ∈ ({i.val, i'.val, j.val, j'.val} : Finset ℕ) := by rw [he]; simp
    have n3 : l.val ∈ ({i.val, i'.val, j.val, j'.val} : Finset ℕ) := by rw [he]; simp
    have n4 : l'.val ∈ ({i.val, i'.val, j.val, j'.val} : Finset ℕ) := by rw [he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4 n1 n2 n3 n4
    refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega
  have hrange : N4 ≤ (Finset.range K0).card := by rw [Finset.card_range]; exact hK0
  rcases hN4 (Finset.range K0) hrange col with ⟨T, hTS, hTcard, hTcol⟩ | ⟨T, hTS, hTcard, hTcol⟩
  all_goals
    let emb := T.orderEmbOfFin hTcard
    have hembK : ∀ i, emb i < K0 := fun i =>
      Finset.mem_range.mp (hTS (T.orderEmbOfFin_mem hTcard i))
    let e : Fin K ↪o Fin K0 := OrderEmbedding.ofStrictMono (fun i => ⟨emb i, hembK i⟩)
      (fun i j hij => by show emb i < emb j; exact emb.strictMono hij)
    have hsubT : ∀ m1 m2 m3 m4 : Fin K,
        ({(e m1).val, (e m2).val, (e m3).val, (e m4).val} : Finset ℕ) ⊆ T := by
      intro m1 m2 m3 m4 x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact T.orderEmbOfFin_mem hTcard _
    refine ⟨e, ?_⟩
    have hb := h.comp e
  · left
    refine hb.toHyp ?_
    intro i i' j j' h1 h2 h3 x hx x' hx' y hy y' hy'
    have hc := hTcol _ (hsubT i i' j j') (hcard4 _ _ _ _ (e.strictMono h1) (e.strictMono h2)
      (e.strictMono h3))
    simp only [col, decide_eq_true_eq] at hc
    have hrep := hc _ _ _ _ (e.strictMono h1) (e.strictMono h2) (e.strictMono h3) rfl
    exact ((h.quad (e.strictMono h1) (e.strictMono h2) (e.strictMono h3)).sign_const
      (hr _) hx (hr _) hy (hr _) hx' (hr _) hy').mp hrep
  · right
    refine hb.toHyp_reflect ?_
    intro i i' j j' h1 h2 h3 x hx x' hx' y hy y' hy'
    have hq := h.quad (e.strictMono h1) (e.strictMono h2) (e.strictMono h3)
    have hc := hTcol _ (hsubT i i' j j') (hcard4 _ _ _ _ (e.strictMono h1) (e.strictMono h2)
      (e.strictMono h3))
    simp only [col, decide_eq_false_iff_not] at hc
    have hnpos : ¬ 0 < vol (r (e i)) (r (e j)) (r (e i')) (r (e j')) := by
      intro hp; apply hc
      intro k k' l l' g1 g2 g3 he
      obtain ⟨u1, u2, u3, u4⟩ := huniq _ _ _ _ _ _ _ _ (e.strictMono h1) (e.strictMono h2)
        (e.strictMono h3) g1 g2 g3 he
      rw [← u1, ← u2, ← u3, ← u4]; exact hp
    have hnpos' : ¬ 0 < vol x y x' y' := fun hp =>
      hnpos ((hq.sign_const hx (hr _) hy (hr _) hx' (hr _) hy' (hr _)).mp hp)
    have hne0 := hq.vol_ne hx hy hx' hy'
    exact lt_of_le_of_ne (not_lt.mp hnpos') hne0

theorem pz_core (t : ℕ) (ht : 1 ≤ t) : ∃ D : ℕ, ∀ n a : ℕ, 2 ≤ n → 2 ≤ a → n ≤ t * a →
    ∀ X : Finset (ℝ^3), Erdos651.IsInGeneralPosition X → ¬ Erdos651.HasConvexSubset n X →
      X.card ≤ D * ((Nat.choose (a + n - 4) (a - 2)) ^ 3 * (Nat.choose (a + n - 4) (a - 2)) ^ 3) := by
  classical
  obtain ⟨N3, hN3⟩ := ramsey_hypergraph 3 (2 * t + 2) (2 * t + 2)
  obtain ⟨N4, hN4⟩ := ramsey_hypergraph 4 N3 N3
  set K0 := max N4 3 with hK0
  obtain ⟨M, hMpos, hpf⟩ := planar_positive_fraction K0 (le_max_right _ _)
  set Q := 8 ^ (K0 ^ 4) with hQ
  refine ⟨M + M ^ (2 * K0) * (24 * Q), ?_⟩
  intro n a hn ha hta X hX hnot
  set Bsq := (Nat.choose (a + n - 4) (a - 2)) ^ 3 * (Nat.choose (a + n - 4) (a - 2)) ^ 3 with hBsq
  have hB1 : 1 ≤ Bsq := by
    have : 0 < Nat.choose (a + n - 4) (a - 2) := Nat.choose_pos (by omega)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  set D := M + M ^ (2 * K0) * (24 * Q)
  have hDle : D ≤ D * Bsq := Nat.le_mul_of_pos_right _ hB1
  obtain ⟨T, hinj, hgp2, hdx⟩ := generic_projection_3d X hX
  set X1 := X.image T with hX1def
  have hX1 : Erdos651.IsInGeneralPosition X1 := linearEquiv_preserves_gp T hX
  have hcard1 : X1.card = X.card := Finset.card_image_of_injective _ T.injective
  have hnot1 : ¬ Erdos651.HasConvexSubset n X1 := fun h => hnot (linearEquiv_reflects_hasConvexSubset T h)
  set Y := X1.image projXY with hYdef
  have hYcard : Y.card = X1.card := Finset.card_image_of_injOn hinj
  by_cases hsmall : Y.card < M
  · have : X.card ≤ D := by omega
    exact this.trans hDle
  obtain ⟨Ys, φ, c, hYsub, hYfrac, hYsep, hYccw⟩ := hpf Y hdx hgp2 (not_lt.mp hsmall)
  let Xs1 : Fin K0 → Finset (ℝ^3) := fun i => X1.filter (fun x => projXY x ∈ Ys i)
  have hX1sub : ∀ i, Xs1 i ⊆ X1 := fun i => Finset.filter_subset _ _
  have hXs1card : ∀ i, (Xs1 i).card = (Ys i).card := by
    intro i
    have himg : (Xs1 i).image projXY = Ys i := by
      ext y; constructor
      · intro hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hYsub i hy)
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hy⟩)
    rw [← himg, Finset.card_image_of_injOn (hinj.mono (by
      intro x hx; exact hX1sub i (Finset.mem_coe.mp hx)))]
  have hproj : ∀ x, projXYLinear x = projXY x := fun x => rfl
  have vsep1 : ∀ i, ∃ (ψ : (ℝ^3) →ₗ[ℝ] ℝ) (c' : ℝ),
      (∀ x ∈ Xs1 i, ψ x < c') ∧ (∀ j, j ≠ i → ∀ x ∈ Xs1 j, c' < ψ x) := by
    intro i
    refine ⟨(φ i).comp projXYLinear, c i, fun x hx => ?_, fun j hj x hx => ?_⟩
    · exact (hYsep i).1 _ (Finset.mem_filter.mp hx).2
    · exact (hYsep i).2 j hj _ (Finset.mem_filter.mp hx).2
  have hXle : ∀ i, X.card ≤ M ^ (2 * K0) * (Xs1 i).card := by
    intro i; rw [hXs1card, ← hcard1, ← hYcard]; exact hYfrac i
  by_cases hbig : ∀ i, 24 * Q ≤ (Xs1 i).card
  swap
  · push_neg at hbig
    obtain ⟨i, hi⟩ := hbig
    have h1 := hXle i
    have h2 : M ^ (2 * K0) * (Xs1 i).card ≤ M ^ (2 * K0) * (24 * Q) :=
      Nat.mul_le_mul_left _ hi.le
    have : X.card ≤ D := by omega
    exact this.trans hDle
  obtain ⟨Xs2, hsub2, hcard2, hsep2⟩ := two_separated_clusters hX1 Xs1 hX1sub vsep1 M hbig
  have base2 : ClusterBase K0 Xs2 := by
    refine ⟨fun i => ?_, hsep2, ?_⟩
    · obtain ⟨ψ, c', h1, h2⟩ := vsep1 i
      exact ⟨ψ, c', fun x hx => h1 x (hsub2 i hx), fun j hj x hx => h2 j hj x (hsub2 j hx)⟩
    · intro a' b' d' hab hbd x hx y hy z hz
      exact hYccw a' b' d' hab hbd _ (Finset.mem_filter.mp (hsub2 _ hx)).2 _
        (Finset.mem_filter.mp (hsub2 _ hy)).2 _ (Finset.mem_filter.mp (hsub2 _ hz)).2
  have hne2 : ∀ i, (Xs2 i).Nonempty := by
    intro i
    have h1 := hbig i; have h2 := hcard2 i
    have hQpos : 0 < Q := by positivity
    rw [← Finset.card_pos]
    by_contra h0; push_neg at h0
    have : (Xs2 i).card = 0 := by omega
    rw [this, mul_zero] at h2
    omega
  have hfin : ∀ i, X.card ≤ M ^ (2 * K0) * Q * (Xs2 i).card := by
    intro i
    calc X.card ≤ M ^ (2 * K0) * (Xs1 i).card := hXle i
      _ ≤ M ^ (2 * K0) * (Q * (Xs2 i).card) := Nat.mul_le_mul_left _ (hcard2 i)
      _ = M ^ (2 * K0) * Q * (Xs2 i).card := by ring
  have hcoef : M ^ (2 * K0) * Q ≤ D := by
    have : M ^ (2 * K0) * Q ≤ M ^ (2 * K0) * (24 * Q) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨e, hcase⟩ := ramsey_quadruples N3 K0 N4 hN4 (le_max_left _ _) base2 hne2
  rcases hcase with hH | hH
  · obtain ⟨m, hm⟩ := cluster_bound t ht N3 hN3 le_rfl hH hX1
      (fun m => (hsub2 _).trans (hX1sub _)) n a ha hn hta hnot1
    calc X.card ≤ M ^ (2 * K0) * Q * (Xs2 (e m)).card := hfin _
      _ ≤ M ^ (2 * K0) * Q * Bsq := Nat.mul_le_mul_left _ hm
      _ ≤ D * Bsq := Nat.mul_le_mul_right _ hcoef
  · have hX2 : Erdos651.IsInGeneralPosition (X1.image reflZ) := linearEquiv_preserves_gp reflZ hX1
    have hnot2 : ¬ Erdos651.HasConvexSubset n (X1.image reflZ) :=
      fun h => hnot1 (linearEquiv_reflects_hasConvexSubset reflZ h)
    obtain ⟨m, hm⟩ := cluster_bound t ht N3 hN3 le_rfl hH hX2
      (fun m => Finset.image_subset_image ((hsub2 _).trans (hX1sub _))) n a ha hn hta hnot2
    rw [Finset.card_image_of_injective _ reflZ.injective] at hm
    calc X.card ≤ M ^ (2 * K0) * Q * (Xs2 (e m)).card := hfin _
      _ ≤ M ^ (2 * K0) * Q * Bsq := Nat.mul_le_mul_left _ hm
      _ ≤ D * Bsq := Nat.mul_le_mul_right _ hcoef

theorem H1_holds : OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1.H1 := by
  obtain ⟨C, hC, hfb⟩ := pz_final_bound
  refine ⟨C, hC, fun t ht => ?_⟩
  obtain ⟨D, hD⟩ := pz_core t (by omega)
  filter_upwards [hfb t ht D, Filter.eventually_ge_atTop (t + 1)] with n hn hnt X hX hnot
  have hdm := Nat.div_add_mod (n + t - 1) t
  have hml := Nat.mod_lt (n + t - 1) (show t > 0 by omega)
  have hta : n ≤ t * ((n + t - 1) / t) := by omega
  have ha : 2 ≤ (n + t - 1) / t := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have h := hD n _ (by omega) ha hta X hX hnot
  have h' : (X.card : ℝ) ≤ (D : ℝ) *
      ((Nat.choose ((n + t - 1) / t + n - 4) ((n + t - 1) / t - 2) : ℕ) : ℝ) ^ 6 := by
    have e : ∀ q : ℕ, q ^ 3 * q ^ 3 = q ^ 6 := fun q => by ring
    rw [e] at h
    exact_mod_cast h
  exact h'.trans hn

end PZ651

theorem OMA.solution : OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1.H1 :=
  PZ651.H1_holds
