import OMAReductions.R_Erdos627_erdos_627_variants_afm_upper_R1
import Mathlib

/-!
# Erdos 627 AFM Upper Bound (H1)

Complete Lean 4 proof of `OMA.R_Erdos627_erdos_627_variants_afm_upper_R1.H1`.
Implements the exponential Ramsey upper bound via the book-algorithm descent
method of Gupta-Ndiaye-Norin-Wei (2024) with verified fixed-point interval
arithmetic certificates, followed by reduction to the clique-independence
bound on arbitrary finite simple graphs.
-/

/- ==================== Section: RamseyDefs.lean ====================-/
namespace Erdos627AFM

open SimpleGraph Finset Real Set

/-- A graph on n vertices has the (k, l)-Ramsey property if every graph on Fin n
contains either a clique of size k or an independent set of size l. -/
def HasRamsey (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique k s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique l s)

lemma hasRamsey_mono_n {k l m n : ℕ} (h : HasRamsey k l m) (hmn : m ≤ n) :
    HasRamsey k l n := by
  intro G
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  rcases h (G.comap f) with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    refine ⟨s.map f, ?_⟩
    have hmap := hs.map (f := f)
    exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f G), hmap.2⟩
  · right
    refine ⟨s.map f, ?_⟩
    have hc : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v
      simp [SimpleGraph.compl_adj, f.injective.eq_iff]
    rw [hc] at hs
    have hmap := hs.map (f := f)
    exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f Gᶜ), hmap.2⟩

lemma hasRamsey_zero_left (l n : ℕ) : HasRamsey 0 l n := fun _ =>
  Or.inl ⟨∅, by simp [SimpleGraph.isNClique_iff]⟩

lemma hasRamsey_zero_right (k n : ℕ) : HasRamsey k 0 n := fun _ =>
  Or.inr ⟨∅, by simp [SimpleGraph.isNClique_iff]⟩

lemma hasRamsey_one_left (l : ℕ) : HasRamsey 1 l 1 := fun _ =>
  Or.inl ⟨{0}, by simp [SimpleGraph.isNClique_iff]⟩

lemma hasRamsey_one_right (k : ℕ) : HasRamsey k 1 1 := fun _ =>
  Or.inr ⟨{0}, by simp [SimpleGraph.isNClique_iff]⟩

lemma hasRamsey_symm {k l n : ℕ} (h : HasRamsey k l n) : HasRamsey l k n := by
  intro G
  rcases h Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inr ⟨s, hs⟩
  · rw [compl_compl] at hs
    exact Or.inl ⟨s, hs⟩

lemma hasRamsey_mono_kl {k₁ k₂ l₁ l₂ n : ℕ} (h : HasRamsey k₂ l₂ n)
    (hk : k₁ ≤ k₂) (hl : l₁ ≤ l₂) : HasRamsey k₁ l₁ n := by
  intro G
  rcases h G with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (hs.card_eq ▸ hk)
    exact Or.inl ⟨t, hs.1.subset hts, htc⟩
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (hs.card_eq ▸ hl)
    exact Or.inr ⟨t, hs.1.subset hts, htc⟩

lemma hasRamsey_of_card_ge {V : Type*} [Fintype V] {k l n : ℕ}
    (h : HasRamsey k l n) (G : SimpleGraph V) (hn : n ≤ Fintype.card V) :
    (∃ s : Finset V, G.IsNClique k s) ∨ (∃ s : Finset V, Gᶜ.IsNClique l s) := by
  have hcard : HasRamsey k l (Fintype.card V) := hasRamsey_mono_n h hn
  let f : Fin (Fintype.card V) ↪ V := (Fintype.equivFin V).symm.toEmbedding
  rcases hcard (G.comap f) with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    refine ⟨s.map f, ?_⟩
    have hmap := hs.map (f := f)
    exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f G), hmap.2⟩
  · right
    refine ⟨s.map f, ?_⟩
    have hc : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v
      simp [SimpleGraph.compl_adj, f.injective.eq_iff]
    rw [hc] at hs
    have hmap := hs.map (f := f)
    exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f Gᶜ), hmap.2⟩

lemma hasRamsey_subset {V : Type*} [DecidableEq V] {k l n : ℕ}
    (h : HasRamsey k l n) (G : SimpleGraph V) (S : Finset V) (hn : n ≤ S.card) :
    (∃ s ⊆ S, G.IsNClique k s) ∨ (∃ s ⊆ S, Gᶜ.IsNClique l s) := by
  let f : S ↪ V := Function.Embedding.subtype _
  have hcard : n ≤ Fintype.card S := by simpa using hn
  rcases hasRamsey_of_card_ge h (G.comap f) hcard with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.1 hx with ⟨y, _, rfl⟩
      exact y.2
    · have hmap := hs.map (f := f)
      exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f G), hmap.2⟩
  · right
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.1 hx with ⟨y, _, rfl⟩
      exact y.2
    · have hc : (G.comap f)ᶜ = Gᶜ.comap f := by
        ext u v
        simp [SimpleGraph.compl_adj, f.injective.eq_iff]
      rw [hc] at hs
      have hmap := hs.map (f := f)
      exact ⟨hmap.1.mono (SimpleGraph.map_comap_le f Gᶜ), hmap.2⟩

lemma hasRamsey_step {k l m₁ m₂ : ℕ} (hm : 1 ≤ m₁ + m₂)
    (h₁ : HasRamsey k (l + 1) m₁) (h₂ : HasRamsey (k + 1) l m₂) :
    HasRamsey (k + 1) (l + 1) (m₁ + m₂) := by
  classical
  intro G
  let v : Fin (m₁ + m₂) := ⟨0, hm⟩
  let rest : Finset (Fin (m₁ + m₂)) := Finset.univ.erase v
  let redN : Finset (Fin (m₁ + m₂)) := rest.filter (G.Adj v)
  let blueN : Finset (Fin (m₁ + m₂)) := rest.filter (fun u => ¬ G.Adj v u)
  have hcard_sum : redN.card + blueN.card = m₁ + m₂ - 1 := by
    have h1 : redN.card + blueN.card = rest.card :=
      Finset.card_filter_add_card_filter_not (s := rest) (p := G.Adj v)
    have h2 : rest.card = m₁ + m₂ - 1 := by simp [rest]
    omega
  by_cases hred : m₁ ≤ redN.card
  · rcases hasRamsey_subset h₁ G redN hred with ⟨s, hs_sub, hs_cl⟩ | ⟨s, _, hs_cl⟩
    · left
      refine ⟨insert v s, ?_⟩
      have hv_not : v ∉ s := fun hvs => by
        have hv_red : v ∈ redN := hs_sub hvs
        exact (Finset.mem_erase.1 (Finset.mem_filter.1 hv_red).1).1 rfl
      refine ⟨?_, by rw [Finset.card_insert_of_notMem hv_not, hs_cl.card_eq]⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact False.elim (hxy rfl)
        · exact (Finset.mem_filter.1 (hs_sub hy')).2
      · rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact (G.adj_comm _ _).1 (Finset.mem_filter.1 (hs_sub hx')).2
        · exact hs_cl.1 hx' hy' hxy
    · exact Or.inr ⟨s, hs_cl⟩
  · have hblue : m₂ ≤ blueN.card := by omega
    rcases hasRamsey_subset h₂ G blueN hblue with ⟨s, _, hs_cl⟩ | ⟨s, hs_sub, hs_cl⟩
    · exact Or.inl ⟨s, hs_cl⟩
    · right
      refine ⟨insert v s, ?_⟩
      have hv_not : v ∉ s := fun hvs => by
        have hv_blue : v ∈ blueN := hs_sub hvs
        exact (Finset.mem_erase.1 (Finset.mem_filter.1 hv_blue).1).1 rfl
      refine ⟨?_, by rw [Finset.card_insert_of_notMem hv_not, hs_cl.card_eq]⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact False.elim (hxy rfl)
        · exact ⟨hxy, (Finset.mem_filter.1 (hs_sub hy')).2⟩
      · rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact ⟨hxy, fun hadj => (Finset.mem_filter.1 (hs_sub hx')).2 ((G.adj_comm _ _).1 hadj)⟩
        · exact hs_cl.1 hx' hy' hxy

lemma hasRamsey_choose (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    HasRamsey k l (Nat.choose (k + l - 2) (k - 1)) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hsub1 : k'.succ + l'.succ - 2 = k' + l' := by omega
  have hsub2 : k'.succ - 1 = k' := by omega
  rw [hsub1, hsub2]
  clear hk hl hsub1 hsub2
  induction s : k' + l' generalizing k' l' with
  | zero =>
    have hk0 : k' = 0 := by omega
    have hl0 : l' = 0 := by omega
    subst hk0; subst hl0
    simpa using hasRamsey_one_left 1
  | succ m ih =>
    cases k' with
    | zero =>
      simpa using hasRamsey_one_left (l' + 1)
    | succ k'' =>
      cases l' with
      | zero =>
        have hch : Nat.choose (k'' + 1 + 0) (k'' + 1) = 1 := by simp
        rw [← s, hch]
        exact hasRamsey_one_right (k'' + 2)
      | succ l'' =>
        have hm1 : k'' + (l'' + 1) = m := by omega
        have hm2 : (k'' + 1) + l'' = m := by omega
        have h1 : HasRamsey (k'' + 1) (l'' + 2) (Nat.choose m k'') :=
          ih k'' (l'' + 1) hm1
        have h2 : HasRamsey (k'' + 2) (l'' + 1) (Nat.choose m (k'' + 1)) :=
          ih (k'' + 1) l'' hm2
        have hsum : Nat.choose (m + 1) (k'' + 1) =
            Nat.choose m k'' + Nat.choose m (k'' + 1) := Nat.choose_succ_succ m k''
        have hpos : 1 ≤ Nat.choose m k'' + Nat.choose m (k'' + 1) := by
          have := Nat.choose_pos (by omega : k'' ≤ m)
          omega
        rw [hsum]
        exact hasRamsey_step hpos h1 h2

lemma exists_hasRamsey (k l : ℕ) : ∃ n : ℕ, HasRamsey k l n := by
  by_cases hk : k = 0
  · subst hk; exact ⟨0, hasRamsey_zero_left l 0⟩
  by_cases hl : l = 0
  · subst hl; exact ⟨0, hasRamsey_zero_right k 0⟩
  exact ⟨Nat.choose (k + l - 2) (k - 1), hasRamsey_choose k l (by omega) (by omega)⟩

/-- Classical two-color Ramsey number R(k, l). -/
noncomputable def ramsey (k l : ℕ) : ℕ :=
  by classical exact Nat.find (exists_hasRamsey k l)

lemma ramsey_spec (k l : ℕ) : HasRamsey k l (ramsey k l) := by
  classical
  exact Nat.find_spec (exists_hasRamsey k l)

lemma ramsey_le_of_hasRamsey {k l n : ℕ} (h : HasRamsey k l n) : ramsey k l ≤ n := by
  classical
  exact Nat.find_min' (exists_hasRamsey k l) h

lemma hasRamsey_of_ramsey_le {k l n : ℕ} (h : ramsey k l ≤ n) : HasRamsey k l n :=
  hasRamsey_mono_n (ramsey_spec k l) h

lemma ramsey_pos {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) : 1 ≤ ramsey k l := by
  by_contra h
  have h0 : ramsey k l = 0 := by omega
  have hr := ramsey_spec k l
  rw [h0] at hr
  rcases hr ⊥ with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hse : s = ∅ := Finset.eq_empty_of_isEmpty s
    have hsc := hs.card_eq
    rw [hse, Finset.card_empty] at hsc
    omega
  · have hse : s = ∅ := Finset.eq_empty_of_isEmpty s
    have hsc := hs.card_eq
    rw [hse, Finset.card_empty] at hsc
    omega

lemma ramsey_symm (k l : ℕ) : ramsey k l = ramsey l k :=
  le_antisymm
    (ramsey_le_of_hasRamsey (hasRamsey_symm (ramsey_spec l k)))
    (ramsey_le_of_hasRamsey (hasRamsey_symm (ramsey_spec k l)))

lemma ramsey_mono {k₁ k₂ l₁ l₂ : ℕ} (hk : k₁ ≤ k₂) (hl : l₁ ≤ l₂) :
    ramsey k₁ l₁ ≤ ramsey k₂ l₂ :=
  ramsey_le_of_hasRamsey (hasRamsey_mono_kl (ramsey_spec k₂ l₂) hk hl)

lemma ramsey_one_left (l : ℕ) (hl : 1 ≤ l) : ramsey 1 l = 1 :=
  le_antisymm (ramsey_le_of_hasRamsey (hasRamsey_one_left l)) (ramsey_pos le_rfl hl)

lemma ramsey_one_right (k : ℕ) (hk : 1 ≤ k) : ramsey k 1 = 1 :=
  le_antisymm (ramsey_le_of_hasRamsey (hasRamsey_one_right k)) (ramsey_pos hk le_rfl)

lemma ramsey_step_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ramsey (k + 1) (l + 1) ≤ ramsey k (l + 1) + ramsey (k + 1) l := by
  have hpos : 1 ≤ ramsey k (l + 1) + ramsey (k + 1) l := by
    have := ramsey_pos hk (by omega : 1 ≤ l + 1)
    omega
  exact ramsey_le_of_hasRamsey (hasRamsey_step hpos (ramsey_spec k (l + 1)) (ramsey_spec (k + 1) l))

lemma ramsey_le_choose {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ramsey k l ≤ Nat.choose (k + l - 2) (k - 1) :=
  ramsey_le_of_hasRamsey (hasRamsey_choose k l hk hl)

lemma lt_ramsey_of_cliqueNum_indepNum {n : ℕ} (H : SimpleGraph (Fin n)) :
    n < ramsey (H.cliqueNum + 1) (H.indepNum + 1) := by
  by_contra h
  have hle : ramsey (H.cliqueNum + 1) (H.indepNum + 1) ≤ n := by omega
  rcases hasRamsey_of_ramsey_le hle H with ⟨s, hs⟩ | ⟨s, hs⟩
  · have h1 := hs.isClique.card_le_cliqueNum
    have h2 := hs.card_eq
    omega
  · have h1 : s.card ≤ H.indepNum := by
      have hc : H.IsIndepSet (s : Set (Fin n)) := by
        simpa [SimpleGraph.isClique_compl] using hs.isClique
      exact hc.card_le_indepNum
    have h2 := hs.card_eq
    omega

/-- Observation 2 in GNNW: R(k, l) ≤ x^{-(k-1)} (1 - x)^{-(l-1)} for 0 < x < 1. -/
lemma ramsey_le_inv_pow {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (ramsey k l : ℝ) ≤ (x ^ (k - 1))⁻¹ * ((1 - x) ^ (l - 1))⁻¹ := by
  have hx1' : 0 < 1 - x := sub_pos.2 hx1
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hsk : k'.succ - 1 = k' := by omega
  have hsl : l'.succ - 1 = l' := by omega
  rw [hsk, hsl]
  clear hk hl hsk hsl
  induction s : k' + l' generalizing k' l' with
  | zero =>
    have hk0 : k' = 0 := by omega
    have hl0 : l' = 0 := by omega
    subst hk0; subst hl0
    simp [ramsey_one_left 1 le_rfl]
  | succ m ih =>
    cases k' with
    | zero =>
      rw [ramsey_one_left (l' + 1) (by omega)]
      simp only [Nat.cast_one, pow_zero, inv_one, one_mul]
      have hle : (1 - x) ^ l' ≤ 1 := pow_le_one₀ hx1'.le (by linarith)
      exact one_le_inv₀ (pow_pos hx1' _) |>.2 hle
    | succ k'' =>
      cases l' with
      | zero =>
        rw [ramsey_one_right (k'' + 2) (by omega)]
        simp only [Nat.cast_one, pow_zero, inv_one, mul_one]
        have hle : x ^ (k'' + 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
        exact one_le_inv₀ (pow_pos hx0 _) |>.2 hle
      | succ l'' =>
        have hstep : (ramsey (k'' + 2) (l'' + 2) : ℝ) ≤
            (ramsey (k'' + 1) (l'' + 2) : ℝ) + (ramsey (k'' + 2) (l'' + 1) : ℝ) := by
          exact_mod_cast ramsey_step_le (by omega) (by omega)
        have ih1 := ih k'' (l'' + 1) (by omega)
        have ih2 := ih (k'' + 1) l'' (by omega)
        have hpow1 : (x ^ k'')⁻¹ = x * (x ^ (k'' + 1))⁻¹ := by
          rw [pow_succ, mul_inv]; field_simp
        have hpow2 : ((1 - x) ^ l'')⁻¹ = (1 - x) * ((1 - x) ^ (l'' + 1))⁻¹ := by
          rw [pow_succ, mul_inv]; field_simp
        calc
          (ramsey (k'' + 2) (l'' + 2) : ℝ)
            ≤ (x ^ k'')⁻¹ * ((1 - x) ^ (l'' + 1))⁻¹ +
              (x ^ (k'' + 1))⁻¹ * ((1 - x) ^ l'')⁻¹ := hstep.trans (add_le_add ih1 ih2)
          _ = (x + (1 - x)) * ((x ^ (k'' + 1))⁻¹ * ((1 - x) ^ (l'' + 1))⁻¹) := by
              rw [hpow1, hpow2]; ring
          _ = (x ^ (k'' + 1))⁻¹ * ((1 - x) ^ (l'' + 1))⁻¹ := by ring

lemma ramsey_le_pow_add {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ramsey k m ≤ (k + m) ^ m := by
  have h1 : ramsey k m ≤ Nat.choose (k + m - 2) (m - 1) := by
    rw [ramsey_symm]
    have h2 := ramsey_le_choose hm hk
    have h3 : m + k - 2 = k + m - 2 := by omega
    rwa [h3] at h2
  have h2 : Nat.choose (k + m - 2) (m - 1) ≤ (k + m - 2) ^ (m - 1) := by
    have hdesc : Nat.descFactorial (k + m - 2) (m - 1) ≤ (k + m - 2) ^ (m - 1) :=
      Nat.descFactorial_le_pow (k + m - 2) (m - 1)
    have hch : Nat.choose (k + m - 2) (m - 1) ≤ Nat.descFactorial (k + m - 2) (m - 1) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    exact hch.trans hdesc
  have h3 : (k + m - 2) ^ (m - 1) ≤ (k + m) ^ (m - 1) :=
    Nat.pow_le_pow_left (by omega) _
  have h4 : (k + m) ^ (m - 1) ≤ (k + m) ^ m :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact h1.trans (h2.trans (h3.trans h4))

/-- Elementary entropy upper bound on binomial coefficients:
choose(a + b, a) ≤ exp((a + b) * binEntropy (a / (a + b))). -/
lemma choose_le_exp_binEntropy {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Nat.choose (a + b) a : ℝ) ≤
      Real.exp (((a : ℝ) + b) * Real.binEntropy ((a : ℝ) / ((a : ℝ) + b))) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) + b := by positivity
  set x : ℝ := (a : ℝ) / ((a : ℝ) + b)
  have hx0 : 0 < x := div_pos ha0 hab
  have h1x : 1 - x = (b : ℝ) / ((a : ℝ) + b) := by
    dsimp [x]; field_simp; ring
  have h1x0 : 0 < 1 - x := by rw [h1x]; exact div_pos hb0 hab
  have hbinom : (Nat.choose (a + b) a : ℝ) * x ^ a * (1 - x) ^ b ≤ 1 := by
    have hsum : (x + (1 - x)) ^ (a + b) = 1 := by rw [add_sub_cancel, one_pow]
    have hmem : a ∈ Finset.range (a + b + 1) := Finset.mem_range.2 (by omega)
    have hterm := Finset.single_le_sum
      (f := fun m => x ^ m * (1 - x) ^ (a + b - m) * (Nat.choose (a + b) m : ℝ))
      (fun m _ => by positivity) hmem
    simp only [Nat.add_sub_cancel_left] at hterm
    rw [← add_pow, hsum] at hterm
    linarith
  have hpos : 0 < x ^ a * (1 - x) ^ b := by positivity
  have hle : (Nat.choose (a + b) a : ℝ) ≤ (x ^ a * (1 - x) ^ b)⁻¹ := by
    rw [le_inv_comm₀ (by exact_mod_cast Nat.choose_pos (by omega : a ≤ a + b)) hpos]
    have h1 : (Nat.choose (a + b) a : ℝ) * (x ^ a * (1 - x) ^ b) ≤ 1 := by
      linarith
    have hch : (0 : ℝ) < (Nat.choose (a + b) a : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : a ≤ a + b)
    rw [inv_eq_one_div, le_div_iff₀ hch]
    linarith
  have hexp : (x ^ a * (1 - x) ^ b)⁻¹ =
      Real.exp (((a : ℝ) + b) * Real.binEntropy x) := by
    have hlog : Real.log ((x ^ a * (1 - x) ^ b)⁻¹) =
        ((a : ℝ) + b) * Real.binEntropy x := by
      rw [Real.log_inv, Real.log_mul (pow_ne_zero _ hx0.ne') (pow_ne_zero _ h1x0.ne'),
          Real.log_pow, Real.log_pow, Real.binEntropy]
      rw [Real.log_inv, Real.log_inv]
      have hax : ((a : ℝ) + b) * x = a := by dsimp [x]; field_simp
      have hbx : ((a : ℝ) + b) * (1 - x) = b := by rw [h1x]; field_simp
      calc
        -((a : ℝ) * Real.log x + (b : ℝ) * Real.log (1 - x))
          = ((a : ℝ) + b) * x * (-Real.log x) + ((a : ℝ) + b) * (1 - x) * (-Real.log (1 - x)) := by
            rw [hax, hbx]; ring
        _ = ((a : ℝ) + b) * (x * -Real.log x + (1 - x) * -Real.log (1 - x)) := by ring
    rw [← hlog, Real.exp_log (inv_pos.2 hpos)]
  exact hle.trans_eq hexp

/-- The dual Ramsey region R from GNNW Section 3:
(x, y) ∈ InR iff for every 0 < x' < x and 0 < y' < y, eventually
R(k, l) ≤ (x')^{-k} (y')^{-l} for k + l sufficiently large. -/
def InR (x y : ℝ) : Prop :=
  0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
  ∀ x' : ℝ, 0 < x' → x' < x → ∀ y' : ℝ, 0 < y' → y' < y →
    ∃ N : ℕ, ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → N ≤ k + l →
      (ramsey k l : ℝ) ≤ (x' ^ k)⁻¹ * (y' ^ l)⁻¹

lemma inR_es {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : InR x (1 - x) := by
  refine ⟨hx0, hx1, sub_pos.2 hx1, by linarith, ?_⟩
  intro x' hx'0 hx'x y' hy'0 hy'y
  refine ⟨0, fun k l hk hl _ => ?_⟩
  have h1 := ramsey_le_inv_pow hx0 hx1 hk hl
  have h2 : (x ^ (k - 1))⁻¹ ≤ (x' ^ k)⁻¹ := by
    have hx'1 : x' ≤ 1 := le_of_lt (hx'x.trans hx1)
    have hpow : x' ^ k ≤ x ^ (k - 1) := by
      calc x' ^ k ≤ x' ^ (k - 1) := pow_le_pow_of_le_one hx'0.le hx'1 (by omega)
        _ ≤ x ^ (k - 1) := pow_le_pow_left₀ hx'0.le hx'x.le _
    exact inv_anti₀ (pow_pos hx'0 _) hpow
  have h3 : ((1 - x) ^ (l - 1))⁻¹ ≤ (y' ^ l)⁻¹ := by
    have hy'1 : y' ≤ 1 := by linarith
    have hpow : y' ^ l ≤ (1 - x) ^ (l - 1) := by
      calc y' ^ l ≤ y' ^ (l - 1) := pow_le_pow_of_le_one hy'0.le hy'1 (by omega)
        _ ≤ (1 - x) ^ (l - 1) := pow_le_pow_left₀ hy'0.le hy'y.le _
    exact inv_anti₀ (pow_pos hy'0 _) hpow
  exact h1.trans (mul_le_mul h2 h3 (by positivity) (by positivity))

lemma inR_mono {x y x₁ y₁ : ℝ} (h : InR x y)
    (hx0 : 0 < x₁) (hxx : x₁ ≤ x) (hy0 : 0 < y₁) (hyy : y₁ ≤ y) : InR x₁ y₁ := by
  rcases h with ⟨_, hx1, _, hy1, hR⟩
  refine ⟨hx0, hxx.trans_lt hx1, hy0, hyy.trans_lt hy1, ?_⟩
  intro x' hx'0 hx'1 y' hy'0 hy'1
  exact hR x' hx'0 (hx'1.trans_le hxx) y' hy'0 (hy'1.trans_le hyy)

/-- Observation 5(4) in GNNW: if for every ε > 0 eventually R(k, l) ≤ exp(ε(k+l)) x^{-k} y^{-l}
for k, l ≥ 1 with k + l large (or k ≥ N₀ and l ≥ N₀), then InR x y. -/
lemma inR_of_asymp {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      (ramsey k l : ℝ) ≤ (x ^ k)⁻¹ * (y ^ l)⁻¹ * Real.exp (ε * ((k : ℝ) + l))) :
    InR x y := by
  refine ⟨hx0, hx1, hy0, hy1, ?_⟩
  intro x' hx'0 hx'x y' hy'0 hy'y
  have hrx : 0 < Real.log (x / x') := Real.log_pos ((one_lt_div hx'0).2 hx'x)
  have hry : 0 < Real.log (y / y') := Real.log_pos ((one_lt_div hy'0).2 hy'y)
  set η : ℝ := min (Real.log (x / x')) (Real.log (y / y'))
  have hη : 0 < η := lt_min hrx hry
  obtain ⟨N₀, hN₀⟩ := h (η / 2) (by linarith)
  set n : ℕ := max N₀ 1
  have hn1 : 1 ≤ n := le_max_right _ _
  have hlogx' : 0 < -Real.log x' := neg_pos.2 (Real.log_neg hx'0 (hx'x.trans hx1))
  have hlogy' : 0 < -Real.log y' := neg_pos.2 (Real.log_neg hy'0 (hy'y.trans hy1))
  have hlogx : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx0 hx1)
  have hlogy : 0 < -Real.log y := neg_pos.2 (Real.log_neg hy0 hy1)
  -- Choose M so that (η / 2) * (M - n) ≥ n * (-log x - log y + η / 2)
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt ((n : ℝ) * (-Real.log x - Real.log y + η / 2) / (η / 2))
  refine ⟨max (2 * n) (M₀ + n), fun k l hk hl hkl => ?_⟩
  have hpow_ratio : ∀ (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (m : ℕ),
      (u ^ m)⁻¹ = (v ^ m)⁻¹ * Real.exp (-(Real.log (u / v) * m)) := by
    intro u v hu hv m
    have h1 : Real.exp (-(Real.log (u / v) * (m : ℝ))) = ((u / v) ^ m)⁻¹ := by
      rw [Real.exp_neg, mul_comm (Real.log (u / v)), Real.exp_nat_mul,
          Real.exp_log (div_pos hu hv)]
    rw [h1, div_pow, inv_div]
    have hup : u ^ m ≠ 0 := (pow_pos hu m).ne'
    have hvp : v ^ m ≠ 0 := (pow_pos hv m).ne'
    field_simp
  have hpow_exp : ∀ (u : ℝ) (hu : 0 < u) (m : ℕ),
      (u ^ m)⁻¹ = Real.exp (-(Real.log u * m)) := by
    intro u hu m
    rw [Real.exp_neg, mul_comm (Real.log u), Real.exp_nat_mul, Real.exp_log hu]
  have hbase : ∀ a b : ℕ, n ≤ a → n ≤ b →
      (ramsey a b : ℝ) ≤ (x' ^ a)⁻¹ * (y' ^ b)⁻¹ * Real.exp (-(η / 2) * ((a : ℝ) + b)) := by
    intro a b ha hb
    have h1 := hN₀ a b ((le_max_left _ _).trans ha) ((le_max_left _ _).trans hb)
    have hxx' := hpow_ratio x x' hx0 hx'0 a
    have hyy' := hpow_ratio y y' hy0 hy'0 b
    have hexp_le : Real.exp (-(Real.log (x / x') * a)) * Real.exp (-(Real.log (y / y') * b)) *
        Real.exp ((η / 2) * ((a : ℝ) + b)) ≤ Real.exp (-(η / 2) * ((a : ℝ) + b)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hηx : η ≤ Real.log (x / x') := min_le_left _ _
      have hηy : η ≤ Real.log (y / y') := min_le_right _ _
      nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
    calc
      (ramsey a b : ℝ)
        ≤ (x ^ a)⁻¹ * (y ^ b)⁻¹ * Real.exp ((η / 2) * ((a : ℝ) + b)) := h1
      _ = (x' ^ a)⁻¹ * (y' ^ b)⁻¹ * (Real.exp (-(Real.log (x / x') * a)) *
          Real.exp (-(Real.log (y / y') * b)) * Real.exp ((η / 2) * ((a : ℝ) + b))) := by
            rw [hxx', hyy']; ring
      _ ≤ (x' ^ a)⁻¹ * (y' ^ b)⁻¹ * Real.exp (-(η / 2) * ((a : ℝ) + b)) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
  by_cases hkn : n ≤ k
  · by_cases hln : n ≤ l
    · have h1 := hbase k l hkn hln
      have hexp1 : Real.exp (-(η / 2) * ((k : ℝ) + l)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) l])
      calc (ramsey k l : ℝ)
          ≤ (x' ^ k)⁻¹ * (y' ^ l)⁻¹ * Real.exp (-(η / 2) * ((k : ℝ) + l)) := h1
        _ ≤ (x' ^ k)⁻¹ * (y' ^ l)⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = (x' ^ k)⁻¹ * (y' ^ l)⁻¹ := mul_one _
    · have hl_lt : l ≤ n := by omega
      have hkm : M₀ ≤ k := by
        have : M₀ + n ≤ k + l := (le_max_right _ _).trans hkl
        omega
      have h1 : (ramsey k l : ℝ) ≤ (ramsey k n : ℝ) := by
        exact_mod_cast ramsey_mono le_rfl hl_lt
      have h2 := hN₀ k n ((le_max_left _ _).trans hkn) (le_max_left _ _)
      have hxx' := hpow_ratio x x' hx0 hx'0 k
      have hyn := hpow_exp y hy0 n
      have hηk : (η / 2) * (k : ℝ) ≥ (n : ℝ) * (-Real.log x - Real.log y + η / 2) := by
        have hM' : ((n : ℝ) * (-Real.log x - Real.log y + η / 2)) / (η / 2) < (k : ℝ) :=
          hM₀.trans_le (by exact_mod_cast hkm)
        exact ((div_lt_iff₀ (by linarith : 0 < η / 2)).1 hM').le.trans_eq (mul_comm _ _)
      have hexp_le : Real.exp (-(Real.log (x / x') * k)) * Real.exp (-(Real.log y * n)) *
          Real.exp ((η / 2) * ((k : ℝ) + n)) ≤ 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_one_iff.2
        have hηx : η ≤ Real.log (x / x') := min_le_left _ _
        nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]
      have hyl : (1 : ℝ) ≤ (y' ^ l)⁻¹ :=
        (one_le_inv₀ (pow_pos hy'0 l)).2 (pow_le_one₀ hy'0.le (hy'y.trans hy1).le)
      calc (ramsey k l : ℝ)
          ≤ (x ^ k)⁻¹ * (y ^ n)⁻¹ * Real.exp ((η / 2) * ((k : ℝ) + n)) := h1.trans h2
        _ = (x' ^ k)⁻¹ * (Real.exp (-(Real.log (x / x') * k)) * Real.exp (-(Real.log y * n)) *
            Real.exp ((η / 2) * ((k : ℝ) + n))) := by rw [hxx', hyn]; ring
        _ ≤ (x' ^ k)⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ ≤ (x' ^ k)⁻¹ * (y' ^ l)⁻¹ := mul_le_mul_of_nonneg_left hyl (by positivity)
  · have hk_lt : k ≤ n := by omega
    have hln : n ≤ l := by
      have : 2 * n ≤ k + l := (le_max_left _ _).trans hkl
      omega
    have hlm : M₀ ≤ l := by
      have : M₀ + n ≤ k + l := (le_max_right _ _).trans hkl
      omega
    have h1 : (ramsey k l : ℝ) ≤ (ramsey n l : ℝ) := by
      exact_mod_cast ramsey_mono hk_lt le_rfl
    have h2 := hN₀ n l (le_max_left _ _) ((le_max_left _ _).trans hln)
    have hyy' := hpow_ratio y y' hy0 hy'0 l
    have hxn := hpow_exp x hx0 n
    have hηl : (η / 2) * (l : ℝ) ≥ (n : ℝ) * (-Real.log x - Real.log y + η / 2) := by
      have hM' : ((n : ℝ) * (-Real.log x - Real.log y + η / 2)) / (η / 2) < (l : ℝ) :=
        hM₀.trans_le (by exact_mod_cast hlm)
      exact ((div_lt_iff₀ (by linarith : 0 < η / 2)).1 hM').le.trans_eq (mul_comm _ _)
    have hexp_le : Real.exp (-(Real.log x * n)) * Real.exp (-(Real.log (y / y') * l)) *
        Real.exp ((η / 2) * ((n : ℝ) + l)) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_one_iff.2
      have hηy : η ≤ Real.log (y / y') := min_le_right _ _
      nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) n]
    have hxk : (1 : ℝ) ≤ (x' ^ k)⁻¹ :=
      (one_le_inv₀ (pow_pos hx'0 k)).2 (pow_le_one₀ hx'0.le (hx'x.trans hx1).le)
    calc (ramsey k l : ℝ)
        ≤ (x ^ n)⁻¹ * (y ^ l)⁻¹ * Real.exp ((η / 2) * ((n : ℝ) + l)) := h1.trans h2
      _ = (y' ^ l)⁻¹ * (Real.exp (-(Real.log x * n)) * Real.exp (-(Real.log (y / y') * l)) *
          Real.exp ((η / 2) * ((n : ℝ) + l))) := by rw [hyy', hxn]; ring
      _ ≤ (y' ^ l)⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = 1 * (y' ^ l)⁻¹ := by ring
      _ ≤ (x' ^ k)⁻¹ * (y' ^ l)⁻¹ := mul_le_mul_of_nonneg_right hxk (by positivity)

end Erdos627AFM

/- ==================== Section: BookHelpers.lean ====================-/
namespace Erdos627AFM

open SimpleGraph Finset Real Set Filter

section GraphHelpers

variable {V : Type*}

/-- Number of red edges (edges of G) between X and Y, counted as ordered pairs (x, y) ∈ X × Y. -/
noncomputable def redEdges (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  by classical exact ∑ x ∈ X, (Y.filter (G.Adj x)).card

/-- Red edge density between X and Y; equals 0 if either set is empty. -/
noncomputable def dens (G : SimpleGraph V) (X Y : Finset V) : ℝ :=
  (redEdges G X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

/-- A candidate (X, Y) is (k, l, t)-good if X ∪ Y has a red K_k, X has a blue K_t,
or Y has a blue K_l. -/
def IsGood [DecidableEq V] (G : SimpleGraph V) (k l t : ℕ) (X Y : Finset V) : Prop :=
  (∃ s ⊆ X ∪ Y, G.IsNClique k s) ∨
  (∃ s ⊆ X, Gᶜ.IsNClique t s) ∨
  (∃ s ⊆ Y, Gᶜ.IsNClique l s)

lemma redEdges_eq_sum_card_filter (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    redEdges G X Y = ∑ x ∈ X, (Y.filter (G.Adj x)).card := by
  classical
  unfold redEdges
  refine Finset.sum_congr rfl fun x _ => congrArg Finset.card ?_
  ext y; simp

lemma redEdges_comm (G : SimpleGraph V) (X Y : Finset V) :
    redEdges G X Y = redEdges G Y X := by
  classical
  simp only [redEdges, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases h : G.Adj x y
  · simp [h, (G.adj_comm _ _).1 h]
  · have h' : ¬ G.Adj y x := fun hyx => h ((G.adj_comm _ _).1 hyx)
    simp [h, h']

lemma redEdges_le_card_mul (G : SimpleGraph V) (X Y : Finset V) :
    redEdges G X Y ≤ X.card * Y.card := by
  classical
  unfold redEdges
  calc ∑ x ∈ X, (Y.filter (G.Adj x)).card
      ≤ ∑ _x ∈ X, Y.card := Finset.sum_le_sum fun x _ => Finset.card_filter_le _ _
    _ = X.card * Y.card := by simp

lemma dens_nonneg (G : SimpleGraph V) (X Y : Finset V) : 0 ≤ dens G X Y := by
  unfold dens; positivity

lemma dens_le_one (G : SimpleGraph V) (X Y : Finset V) : dens G X Y ≤ 1 := by
  unfold dens
  by_cases h : (X.card : ℝ) * (Y.card : ℝ) = 0
  · simp [h]
  · have hpos : 0 < (X.card : ℝ) * (Y.card : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_le_one hpos]
    exact_mod_cast redEdges_le_card_mul G X Y

lemma dens_mul_cards (G : SimpleGraph V) {X Y : Finset V} (hX : X.Nonempty) (hY : Y.Nonempty) :
    dens G X Y * (X.card : ℝ) * (Y.card : ℝ) = (redEdges G X Y : ℝ) := by
  unfold dens
  have hX0 : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_pos.ne'
  have hY0 : (Y.card : ℝ) ≠ 0 := by exact_mod_cast hY.card_pos.ne'
  field_simp

lemma redEdges_disj_union_left [DecidableEq V] (G : SimpleGraph V) {X₁ X₂ Y : Finset V} (hd : Disjoint X₁ X₂) :
    redEdges G (X₁ ∪ X₂) Y = redEdges G X₁ Y + redEdges G X₂ Y := by
  classical
  simp only [redEdges, Finset.sum_union hd]

lemma redEdges_erase_left [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {X Y : Finset V}
    {v : V} (hv : v ∈ X) :
    redEdges G (X.erase v) Y + (Y.filter (G.Adj v)).card = redEdges G X Y := by
  rw [redEdges_eq_sum_card_filter, redEdges_eq_sum_card_filter]
  exact Finset.sum_erase_add (s := X) (f := fun x => (Y.filter (G.Adj x)).card) hv

/-- Lemma 8 in GNNW (convexity of density):
∑_{v ∈ X} d(X, N_R(v) ∩ Y) * |N_R(v) ∩ Y| ≥ e_R(X, Y) * d(X, Y). -/
lemma sum_dens_redNbhd_ge (G : SimpleGraph V) [DecidableRel G.Adj] {X Y : Finset V}
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    (redEdges G X Y : ℝ) * dens G X Y ≤
      ∑ v ∈ X, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) := by
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  -- Multiply both sides by |X|
  suffices h : (X.card : ℝ) * ((redEdges G X Y : ℝ) * dens G X Y) ≤
      (X.card : ℝ) * ∑ v ∈ X, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) by
    exact le_of_mul_le_mul_left h hXpos
  have hlhs : (X.card : ℝ) * ((redEdges G X Y : ℝ) * dens G X Y) =
      (redEdges G X Y : ℝ) ^ 2 / (Y.card : ℝ) := by
    unfold dens
    field_simp [hXpos.ne', hYpos.ne']
  have hrhs : (X.card : ℝ) * ∑ v ∈ X, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) =
      ∑ v ∈ X, (redEdges G X (Y.filter (G.Adj v)) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold dens
    by_cases hYv : (Y.filter (G.Adj v)).card = 0
    · have hemp : Y.filter (G.Adj v) = ∅ := Finset.card_eq_zero.1 hYv
      simp [hemp, redEdges]
    · have hYvpos : (0 : ℝ) < (Y.filter (G.Adj v)).card := by exact_mod_cast Nat.pos_of_ne_zero hYv
      field_simp [hXpos.ne', hYvpos.ne']
  rw [hlhs, hrhs, div_le_iff₀ hYpos]
  -- Double counting: ∑_{v ∈ X} e_R(X, N_R(v) ∩ Y) = ∑_{y ∈ Y} |N_R(y) ∩ X|^2
  have hdouble : ∑ v ∈ X, redEdges G X (Y.filter (G.Adj v)) =
      ∑ y ∈ Y, (X.filter (G.Adj y)).card ^ 2 := by
    calc ∑ v ∈ X, redEdges G X (Y.filter (G.Adj v))
        = ∑ v ∈ X, redEdges G (Y.filter (G.Adj v)) X :=
            Finset.sum_congr rfl fun v _ => redEdges_comm G X _
      _ = ∑ v ∈ X, ∑ y ∈ Y.filter (G.Adj v), (X.filter (G.Adj y)).card := by
            refine Finset.sum_congr rfl fun v _ => redEdges_eq_sum_card_filter G _ X
      _ = ∑ v ∈ X, ∑ y ∈ Y, if G.Adj v y then (X.filter (G.Adj y)).card else 0 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.sum_filter]
      _ = ∑ y ∈ Y, ∑ v ∈ X, if G.Adj v y then (X.filter (G.Adj y)).card else 0 := Finset.sum_comm
      _ = ∑ y ∈ Y, ∑ v ∈ X.filter (G.Adj y), (X.filter (G.Adj y)).card := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun v _ => ?_
            by_cases h : G.Adj v y
            · simp [h, (G.adj_comm _ _).1 h]
            · have h' : ¬ G.Adj y v := fun hyx => h ((G.adj_comm _ _).1 hyx)
              simp [h, h']
      _ = ∑ y ∈ Y, (X.filter (G.Adj y)).card ^ 2 := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_const, smul_eq_mul, sq]
  have hsum_e : (redEdges G X Y : ℝ) = ∑ y ∈ Y, ((X.filter (G.Adj y)).card : ℝ) := by
    rw [redEdges_comm G X Y, redEdges_eq_sum_card_filter]
    push_cast; rfl
  have hdouble_r : (∑ v ∈ X, (redEdges G X (Y.filter (G.Adj v)) : ℝ)) =
      ∑ y ∈ Y, ((X.filter (G.Adj y)).card : ℝ) ^ 2 := by
    exact_mod_cast hdouble
  rw [hsum_e, hdouble_r, mul_comm]
  exact sq_sum_le_card_mul_sum_sq

end GraphHelpers

section BlueBook

/-- Continuous convex extension of x ↦ ∏_{i=0}^{b-1} (x - i) to ℝ, equal to 0 for x ≤ b - 1. -/
noncomputable def fallFactPos (b : ℕ) (x : ℝ) : ℝ :=
  if (b : ℝ) - 1 ≤ x then ∏ i ∈ Finset.range b, (x - (i : ℝ)) else 0

lemma fallFactPos_nat (b n : ℕ) :
    fallFactPos b (n : ℝ) = (b.factorial : ℝ) * (Nat.choose n b : ℝ) := by
  unfold fallFactPos
  by_cases hnb : b ≤ n
  · have hge : (b : ℝ) - 1 ≤ (n : ℝ) := by
      have : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
      linarith
    rw [if_pos hge]
    have hnat : ∏ i ∈ Finset.range b, (n - i) = b.factorial * Nat.choose n b := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    have hcast : (∏ i ∈ Finset.range b, ((n : ℝ) - (i : ℝ))) =
        ((∏ i ∈ Finset.range b, (n - i) : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i < b := Finset.mem_range.1 hi
      rw [Nat.cast_sub (by omega)]
    rw [hcast, hnat, Nat.cast_mul]
  · have hchoose : Nat.choose n b = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero, mul_zero]
    split_ifs with hge
    · -- Only possible if n = b - 1 (when b ≥ 1)
      have hbn : n + 1 = b := by
        have h1 : (b : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h2 : b ≤ n + 1 := by exact_mod_cast h1
        omega
      refine Finset.prod_eq_zero (Finset.mem_range.2 (by omega : n < b)) ?_
      simp
    · rfl

lemma convexOn_prod_linear_Ici (b : ℕ) :
    ConvexOn ℝ (Ici ((b : ℝ) - 1)) (fun x : ℝ => ∏ i ∈ Finset.range b, (x - (i : ℝ))) := by
  -- Prove stronger: nonneg, monotone, convex on Ici (b - 1)
  have hstrong : ∀ m : ℕ, ∀ c : ℝ, (m : ℝ) - 1 ≤ c →
      (∀ x ∈ Ici c, 0 ≤ ∏ i ∈ Finset.range m, (x - (i : ℝ))) ∧
      MonotoneOn (fun x : ℝ => ∏ i ∈ Finset.range m, (x - (i : ℝ))) (Ici c) ∧
      ConvexOn ℝ (Ici c) (fun x : ℝ => ∏ i ∈ Finset.range m, (x - (i : ℝ))) := by
    intro m
    induction m with
    | zero =>
      intro c _
      refine ⟨fun _ _ => by simp, monotoneOn_const, convexOn_const 1 (convex_Ici c)⟩
    | succ m ih =>
      intro c hc
      have hcm : (m : ℝ) - 1 ≤ c := by push_cast at hc; linarith
      obtain ⟨hnn, hmono, hconv⟩ := ih c hcm
      have hfac_nn : ∀ x ∈ Ici c, 0 ≤ x - (m : ℝ) := by
        intro x hx; rw [Set.mem_Ici] at hx; push_cast at hc; linarith
      have hprod_eq : (fun x : ℝ => ∏ i ∈ Finset.range (m + 1), (x - (i : ℝ))) =
          fun x => (∏ i ∈ Finset.range m, (x - (i : ℝ))) * (x - (m : ℝ)) := by
        ext x; exact Finset.prod_range_succ _ _
      refine ⟨fun x hx => by rw [Finset.prod_range_succ]; exact mul_nonneg (hnn x hx) (hfac_nn x hx), ?_, ?_⟩
      · rw [hprod_eq]
        intro x hx y hy hxy
        exact mul_le_mul (hmono hx hy hxy) (by linarith) (hfac_nn x hx) (hnn y hy)
      · rw [hprod_eq]
        refine ⟨convex_Ici c, fun x hx y hy a b ha hb hab => ?_⟩
        have hfc := hconv.2 hx hy ha hb hab
        simp only [smul_eq_mul] at hfc ⊢
        have hlin : a * x + b * y - (m : ℝ) = a * (x - (m : ℝ)) + b * (y - (m : ℝ)) := by
          calc a * x + b * y - (m : ℝ) = a * x + b * y - (a + b) * (m : ℝ) := by rw [hab, one_mul]
            _ = a * (x - (m : ℝ)) + b * (y - (m : ℝ)) := by ring
        have hlin_nn : 0 ≤ a * (x - (m : ℝ)) + b * (y - (m : ℝ)) :=
          add_nonneg (mul_nonneg ha (hfac_nn x hx)) (mul_nonneg hb (hfac_nn y hy))
        have hcheb : (a * (∏ i ∈ Finset.range m, (x - (i : ℝ))) +
            b * (∏ i ∈ Finset.range m, (y - (i : ℝ)))) *
            (a * (x - (m : ℝ)) + b * (y - (m : ℝ))) ≤
            a * ((∏ i ∈ Finset.range m, (x - (i : ℝ))) * (x - (m : ℝ))) +
            b * ((∏ i ∈ Finset.range m, (y - (i : ℝ))) * (y - (m : ℝ))) := by
          have hdiff : (a * ((∏ i ∈ Finset.range m, (x - (i : ℝ))) * (x - (m : ℝ))) +
              b * ((∏ i ∈ Finset.range m, (y - (i : ℝ))) * (y - (m : ℝ)))) -
              (a * (∏ i ∈ Finset.range m, (x - (i : ℝ))) +
                b * (∏ i ∈ Finset.range m, (y - (i : ℝ)))) *
              (a * (x - (m : ℝ)) + b * (y - (m : ℝ))) =
              a * b * ((∏ i ∈ Finset.range m, (x - (i : ℝ))) -
                (∏ i ∈ Finset.range m, (y - (i : ℝ)))) * (x - y) := by
            have ha1 : a * (1 - a) = a * b := by rw [← hab]; ring
            have hb1 : b * (1 - b) = a * b := by rw [← hab]; ring
            calc _ = a * (1 - a) * (∏ i ∈ Finset.range m, (x - (i : ℝ))) * (x - (m : ℝ)) +
                     b * (1 - b) * (∏ i ∈ Finset.range m, (y - (i : ℝ))) * (y - (m : ℝ)) -
                     a * b * ((∏ i ∈ Finset.range m, (x - (i : ℝ))) * (y - (m : ℝ)) +
                       (∏ i ∈ Finset.range m, (y - (i : ℝ))) * (x - (m : ℝ))) := by ring
              _ = a * b * ((∏ i ∈ Finset.range m, (x - (i : ℝ))) -
                    (∏ i ∈ Finset.range m, (y - (i : ℝ)))) * (x - y) := by rw [ha1, hb1]; ring
          have hprod_nn : 0 ≤ ((∏ i ∈ Finset.range m, (x - (i : ℝ))) -
              (∏ i ∈ Finset.range m, (y - (i : ℝ)))) * (x - y) := by
            rcases le_total x y with hxy | hyx
            · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hmono hx hy hxy)) (sub_nonpos.2 hxy)
            · exact mul_nonneg (sub_nonneg.2 (hmono hy hx hyx)) (sub_nonneg.2 hyx)
          have := mul_nonneg (mul_nonneg ha hb) hprod_nn
          linarith
        rw [hlin]
        exact (mul_le_mul_of_nonneg_right hfc hlin_nn).trans hcheb
  exact (hstrong b ((b : ℝ) - 1) le_rfl).2.2

lemma convexOn_fallFactPos (b : ℕ) (hb : 1 ≤ b) : ConvexOn ℝ univ (fallFactPos b) := by
  refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
  set f : ℝ → ℝ := fun z => ∏ i ∈ Finset.range b, (z - (i : ℝ))
  have hconv := convexOn_prod_linear_Ici b
  have hf_nn : ∀ z : ℝ, (b : ℝ) - 1 ≤ z → 0 ≤ f z := fun z hz =>
    Finset.prod_nonneg fun i hi => by
      have hi' : i < b := Finset.mem_range.1 hi
      have hi_le : (i : ℝ) ≤ (b : ℝ) - 1 := by
        have : i + 1 ≤ b := hi'
        have : (i : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast this
        linarith
      linarith
  have hf_zero : f ((b : ℝ) - 1) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_range.2 (by omega : b - 1 < b)) ?_
    rw [Nat.cast_sub hb, Nat.cast_one]; ring
  have hmax : ∀ z : ℝ, fallFactPos b z = if (b : ℝ) - 1 ≤ z then f z else 0 := fun _ => rfl
  simp only [smul_eq_mul]
  by_cases hcomb : (b : ℝ) - 1 ≤ a * x + c * y
  · rw [hmax, if_pos hcomb]
    -- Replace x, y by max x (b-1), max y (b-1)
    let x' := max x ((b : ℝ) - 1)
    let y' := max y ((b : ℝ) - 1)
    have hx' : (b : ℝ) - 1 ≤ x' := le_max_right _ _
    have hy' : (b : ℝ) - 1 ≤ y' := le_max_right _ _
    have hfx' : f x' = fallFactPos b x := by
      rw [hmax]
      by_cases hx : (b : ℝ) - 1 ≤ x
      · rw [if_pos hx, show x' = x from max_eq_left hx]
      · rw [if_neg hx, show x' = (b : ℝ) - 1 from max_eq_right (le_of_not_ge hx), hf_zero]
    have hfy' : f y' = fallFactPos b y := by
      rw [hmax]
      by_cases hy : (b : ℝ) - 1 ≤ y
      · rw [if_pos hy, show y' = y from max_eq_left hy]
      · rw [if_neg hy, show y' = (b : ℝ) - 1 from max_eq_right (le_of_not_ge hy), hf_zero]
    have hle_comb : a * x + c * y ≤ a * x' + c * y' :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hc)
    have hmono : f (a * x + c * y) ≤ f (a * x' + c * y') := by
      refine Finset.prod_le_prod (fun i hi => ?_) (fun i _ => by linarith)
      have hi' : (i : ℝ) ≤ (b : ℝ) - 1 := by
        have : i + 1 ≤ b := Finset.mem_range.1 hi
        have : (i : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast this
        linarith
      linarith
    have hc' : f (a * x' + c * y') ≤ a * f x' + c * f y' := by
      simpa only [smul_eq_mul] using hconv.2 hx' hy' ha hc hac
    rw [hfx', hfy'] at hc'
    exact hmono.trans hc'
  · rw [hmax, if_neg hcomb]
    have hnn : ∀ z, 0 ≤ fallFactPos b z := fun z => by
      rw [hmax]; split_ifs with hz
      · exact hf_nn z hz
      · exact le_rfl
    exact add_nonneg (mul_nonneg ha (hnn x)) (mul_nonneg hc (hnn y))

/-- Algebraic version of Fact 9 in GNNW using Bernoulli's inequality:
∏_{i=0}^{b-1} (σ m - i) ≥ σ^b * (1 - b^2 / (σ m)) * ∏_{i=0}^{b-1} (m - i). -/
lemma fallFact_mul_ge {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {b m : ℕ}
    (hb : 1 ≤ b) (hbm : (b : ℝ) ≤ σ * (m : ℝ) / 2) :
    σ ^ b * (1 - (b : ℝ) ^ 2 / (σ * (m : ℝ))) * (∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ))) ≤
      ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := by
  have hm0 : 0 < σ * (m : ℝ) := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hm_pos : (0 : ℝ) < m := by
    by_contra h
    have : (m : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg m)
    rw [this, mul_zero] at hm0; exact lt_irrefl 0 hm0
  have h1 : ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)) ≤ (m : ℝ) ^ b := by
    calc ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ))
        ≤ ∏ _i ∈ Finset.range b, (m : ℝ) := by
          refine Finset.prod_le_prod (fun i hi => ?_) (fun i _ => by linarith [Nat.cast_nonneg (α := ℝ) i])
          have hi' : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.1 hi
          have : (b : ℝ) ≤ (m : ℝ) := by nlinarith
          linarith
      _ = (m : ℝ) ^ b := by simp
  have h2 : σ ^ b * (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b * (m : ℝ) ^ b ≤
      ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := by
    have hprod_eq : σ ^ b * (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b * (m : ℝ) ^ b =
        ∏ _i ∈ Finset.range b, (σ * (m : ℝ) - (b : ℝ)) := by
      rw [Finset.prod_const, Finset.card_range, ← mul_pow, ← mul_pow]
      congr 1; field_simp [hm0.ne']
    rw [hprod_eq]
    refine Finset.prod_le_prod (fun _ _ => by linarith) (fun i hi => ?_)
    have hi' : (i : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Finset.mem_range.1 hi).le
    linarith
  have hbern : 1 - (b : ℝ) ^ 2 / (σ * (m : ℝ)) ≤ (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b := by
    have hneg : (-2 : ℝ) ≤ -((b : ℝ) / (σ * (m : ℝ))) := by
      have : (b : ℝ) / (σ * (m : ℝ)) ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
      linarith
    have hb_ineq := one_add_mul_le_pow hneg b
    have heq1 : 1 + (b : ℝ) * -((b : ℝ) / (σ * (m : ℝ))) = 1 - (b : ℝ) ^ 2 / (σ * (m : ℝ)) := by ring
    have heq2 : 1 + -((b : ℝ) / (σ * (m : ℝ))) = 1 - (b : ℝ) / (σ * (m : ℝ)) := by ring
    rw [heq1, heq2] at hb_ineq
    exact hb_ineq
  have hnn_prod : 0 ≤ ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)) :=
    Finset.prod_nonneg fun i hi => by
      have hi' : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.1 hi
      have : (b : ℝ) ≤ (m : ℝ) := by nlinarith
      linarith
  have hnn_bern : 0 ≤ (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b :=
    pow_nonneg (by
      have : (b : ℝ) / (σ * (m : ℝ)) ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
      linarith) _
  calc σ ^ b * (1 - (b : ℝ) ^ 2 / (σ * (m : ℝ))) * (∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)))
      ≤ σ ^ b * (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b * (∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ hnn_prod
        exact mul_le_mul_of_nonneg_left hbern (pow_nonneg hσ0.le _)
    _ ≤ σ ^ b * (1 - (b : ℝ) / (σ * (m : ℝ))) ^ b * (m : ℝ) ^ b :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (pow_nonneg hσ0.le _) hnn_bern)
    _ ≤ ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := h2

set_option maxHeartbeats 800000 in
/-- Lemma 10 in GNNW (Blue Book Lemma):
If |X| ≥ 5 m^2, m ≥ 10 μ^{-1} b^2, and at least R(k, m) vertices v ∈ X have
|N_B(v) ∩ X| ≥ μ |X|, then X contains either a red K_k or a blue book (S, T)
with |S| = b and |T| ≥ (μ^b / 2) |X|. -/
lemma blue_book_lemma {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    {b k m : ℕ} (hb : 1 ≤ b) (_hk : 1 ≤ k) (hm : 1 ≤ m)
    (hm_ge : 10 * μ⁻¹ * (b : ℝ) ^ 2 ≤ (m : ℝ))
    (X : Finset V) (hX_ge : 5 * (m : ℝ) ^ 2 ≤ (X.card : ℝ))
    (hW : ramsey k m ≤ (X.filter (fun v => μ * (X.card : ℝ) ≤
      ((X.filter (fun u => v ≠ u ∧ ¬ G.Adj v u)).card : ℝ))).card) :
    (∃ s ⊆ X, G.IsNClique k s) ∨
    (∃ S T : Finset V, S ⊆ X ∧ T ⊆ X ∧ Disjoint S T ∧
      Gᶜ.IsNClique b S ∧
      (∀ u ∈ S, ∀ v ∈ T, Gᶜ.Adj u v) ∧
      μ ^ b / 2 * (X.card : ℝ) ≤ (T.card : ℝ)) := by
  classical
  set W : Finset V := X.filter (fun v => μ * (X.card : ℝ) ≤
    ((X.filter (fun u => v ≠ u ∧ ¬ G.Adj v u)).card : ℝ))
  rcases hasRamsey_subset (ramsey_spec k m) G W hW with ⟨s, hsW, hscl⟩ | ⟨U, hUW, hUcl⟩
  · left
    exact ⟨s, hsW.trans (Finset.filter_subset _ X), hscl⟩
  · right
    have hUX : U ⊆ X := hUW.trans (Finset.filter_subset _ X)
    have hUcard : U.card = m := hUcl.card_eq
    set R : Finset V := X \ U
    have hRsub : R ⊆ X := Finset.sdiff_subset
    have hdisjUR : Disjoint U R := Finset.disjoint_sdiff
    have hRcard : R.card + m = X.card := by
      have h1 : R.card + U.card = X.card := Finset.card_sdiff_add_card_eq_card hUX
      omega
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hb_ge1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hb_pos : (0 : ℝ) < b := by linarith
    have hX_pos : (0 : ℝ) < X.card := by nlinarith
    have hR_pos_nat : 1 ≤ R.card := by
      have h1 : (5 : ℝ) * (m : ℝ) ≤ (X.card : ℝ) := by nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]
      have h2 : 5 * m ≤ X.card := by exact_mod_cast h1
      omega
    have hR_pos : (0 : ℝ) < R.card := by exact_mod_cast hR_pos_nat
    -- Blue degree of each u ∈ U into R is ≥ μ |X| - m
    let blueNbhdR (v : V) : Finset V := R.filter (Gᶜ.Adj v)
    let blueNbhdU (v : V) : Finset V := U.filter (Gᶜ.Adj v)
    -- Define σ = (∑_{u ∈ U} |N_B(u) ∩ R|) / (m * |R|)
    let eB : ℕ := ∑ u ∈ U, (blueNbhdR u).card
    let σ : ℝ := (eB : ℝ) / ((m : ℝ) * (R.card : ℝ))
    have hdeg_u : ∀ u ∈ U, μ * (X.card : ℝ) - (m : ℝ) ≤ ((blueNbhdR u).card : ℝ) := by
      intro u hu
      have huW : u ∈ W := hUW hu
      have hμX : μ * (X.card : ℝ) ≤ ((X.filter (fun w => u ≠ w ∧ ¬ G.Adj u w)).card : ℝ) :=
        (Finset.mem_filter.1 huW).2
      have hsub : X.filter (fun w => u ≠ w ∧ ¬ G.Adj u w) ⊆ blueNbhdR u ∪ U := by
        intro w hw
        rw [Finset.mem_filter] at hw
        by_cases hwU : w ∈ U
        · exact Finset.mem_union_right _ hwU
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hw.1, hwU⟩, hw.2⟩)
      have hcard_le : (X.filter (fun w => u ≠ w ∧ ¬ G.Adj u w)).card ≤ (blueNbhdR u).card + m := by
        calc _ ≤ (blueNbhdR u ∪ U).card := Finset.card_le_card hsub
          _ ≤ (blueNbhdR u).card + U.card := Finset.card_union_le _ _
          _ = (blueNbhdR u).card + m := by rw [hUcard]
      have hcard_le_r : ((X.filter (fun w => u ≠ w ∧ ¬ G.Adj u w)).card : ℝ) ≤
          ((blueNbhdR u).card : ℝ) + (m : ℝ) := by exact_mod_cast hcard_le
      linarith
    have heB_ge : (m : ℝ) * (μ * (X.card : ℝ) - (m : ℝ)) ≤ (eB : ℝ) := by
      have h1 : ∑ _u ∈ U, (μ * (X.card : ℝ) - (m : ℝ)) ≤ ∑ u ∈ U, ((blueNbhdR u).card : ℝ) :=
        Finset.sum_le_sum hdeg_u
      rw [Finset.sum_const, hUcard, nsmul_eq_mul] at h1
      simpa [eB] using h1
    have heB_le : (eB : ℝ) ≤ (m : ℝ) * (R.card : ℝ) := by
      have h1 : eB ≤ ∑ _u ∈ U, R.card := Finset.sum_le_sum fun u _ => Finset.card_filter_le _ _
      rw [Finset.sum_const, hUcard, smul_eq_mul] at h1
      exact_mod_cast h1
    have hσ1 : σ ≤ 1 := (div_le_one (mul_pos hm_pos hR_pos)).2 heB_le
    have hσ_lb1 : μ * (1 - 1 / (5 * (b : ℝ))) ≤ σ := by
      -- First: |X| ≥ 5 m^2 ≥ 5 μ^{-1} m b (since m ≥ 10 μ^{-1} b^2 ≥ μ^{-1} b)
      have hm_ge_b : μ⁻¹ * (b : ℝ) ≤ (m : ℝ) := by
        have hb1 : (b : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
        nlinarith [inv_pos.2 hμ0]
      have hX_ge2 : 5 * μ⁻¹ * (m : ℝ) * (b : ℝ) ≤ (X.card : ℝ) := by
        nlinarith [hm_pos]
      have hm_le_frac : (m : ℝ) ≤ μ * (X.card : ℝ) / (5 * (b : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : (m : ℝ) * (5 * (b : ℝ)) = μ * (5 * μ⁻¹ * (m : ℝ) * (b : ℝ)) := by
          field_simp [hμ0.ne']
        rw [h1]
        exact mul_le_mul_of_nonneg_left hX_ge2 hμ0.le
      have hRX : (R.card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast (by omega : R.card ≤ X.card)
      have hnum : μ * (1 - 1 / (5 * (b : ℝ))) * ((m : ℝ) * (R.card : ℝ)) ≤ (eB : ℝ) := by
        have hfact : μ * (1 - 1 / (5 * (b : ℝ))) * (X.card : ℝ) ≤ μ * (X.card : ℝ) - (m : ℝ) := by
          have : μ * (1 - 1 / (5 * (b : ℝ))) * (X.card : ℝ) =
              μ * (X.card : ℝ) - μ * (X.card : ℝ) / (5 * (b : ℝ)) := by ring
          linarith
        have hnn : 0 ≤ μ * (1 - 1 / (5 * (b : ℝ))) := by
          have : 1 / (5 * (b : ℝ)) ≤ 1 / 5 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          nlinarith
        calc μ * (1 - 1 / (5 * (b : ℝ))) * ((m : ℝ) * (R.card : ℝ))
            = (m : ℝ) * (μ * (1 - 1 / (5 * (b : ℝ))) * (R.card : ℝ)) := by ring
          _ ≤ (m : ℝ) * (μ * (1 - 1 / (5 * (b : ℝ))) * (X.card : ℝ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRX hnn) hm_pos.le
          _ ≤ (m : ℝ) * (μ * (X.card : ℝ) - (m : ℝ)) :=
              mul_le_mul_of_nonneg_left hfact hm_pos.le
          _ ≤ (eB : ℝ) := heB_ge
      exact (le_div_iff₀ (mul_pos hm_pos hR_pos)).2 hnum
    have hσ_half : μ / 2 ≤ σ := by
      have : 1 / (5 * (b : ℝ)) ≤ 1 / 5 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      nlinarith
    have hσ0 : 0 < σ := lt_of_lt_of_le (by linarith) hσ_half
    have hbm_cond : (b : ℝ) ≤ σ * (m : ℝ) / 2 := by
      have h1 : 5 * (b : ℝ) ^ 2 ≤ σ * (m : ℝ) := by
        have h2 : μ * (m : ℝ) ≥ 10 * (b : ℝ) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hm_ge hμ0.le
          have heq : μ * (10 * μ⁻¹ * (b : ℝ) ^ 2) = 10 * (b : ℝ) ^ 2 := by
            field_simp [hμ0.ne']
          linarith
        nlinarith
      nlinarith
    have hb_le_m : b ≤ m := by
      have : (b : ℝ) ≤ (m : ℝ) := by nlinarith
      exact_mod_cast this
    -- Double count sum over S ∈ U.powersetCard b of |T(S)|
    let Tset (S : Finset V) : Finset V := R.filter (fun v => ∀ u ∈ S, Gᶜ.Adj u v)
    have hdouble_T : ∑ S ∈ U.powersetCard b, (Tset S).card =
        ∑ v ∈ R, Nat.choose (blueNbhdU v).card b := by
      calc ∑ S ∈ U.powersetCard b, (Tset S).card
          = ∑ S ∈ U.powersetCard b, ∑ v ∈ R, if ∀ u ∈ S, Gᶜ.Adj u v then 1 else 0 := by
              refine Finset.sum_congr rfl fun S _ => ?_
              dsimp [Tset]; rw [Finset.card_filter]
        _ = ∑ v ∈ R, ∑ S ∈ U.powersetCard b, if ∀ u ∈ S, Gᶜ.Adj u v then 1 else 0 :=
              Finset.sum_comm
        _ = ∑ v ∈ R, ((U.powersetCard b).filter (fun S => ∀ u ∈ S, Gᶜ.Adj u v)).card := by
              refine Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm
        _ = ∑ v ∈ R, ((blueNbhdU v).powersetCard b).card := by
              refine Finset.sum_congr rfl fun v _ => congrArg Finset.card ?_
              ext S
              simp only [Finset.mem_filter, Finset.mem_powersetCard, blueNbhdU]
              constructor
              · rintro ⟨⟨hSU, hSc⟩, hall⟩
                refine ⟨fun u hu => Finset.mem_filter.2 ⟨hSU hu, (Gᶜ.adj_comm _ _).1 (hall u hu)⟩, hSc⟩
              · rintro ⟨hSsub, hSc⟩
                refine ⟨⟨fun u hu => (Finset.mem_filter.1 (hSsub hu)).1, hSc⟩,
                  fun u hu => (Gᶜ.adj_comm _ _).1 (Finset.mem_filter.1 (hSsub hu)).2⟩
        _ = ∑ v ∈ R, Nat.choose (blueNbhdU v).card b := by
              refine Finset.sum_congr rfl fun v _ => Finset.card_powersetCard b _
    -- Double count ∑_{v ∈ R} |N_B(v) ∩ U| = eB = σ * m * |R|
    have hsum_degU : ∑ v ∈ R, (blueNbhdU v).card = eB := by
      calc ∑ v ∈ R, (blueNbhdU v).card
          = ∑ v ∈ R, ∑ u ∈ U, if Gᶜ.Adj v u then 1 else 0 := by
              refine Finset.sum_congr rfl fun v _ => by dsimp [blueNbhdU]; rw [Finset.card_filter]
        _ = ∑ u ∈ U, ∑ v ∈ R, if Gᶜ.Adj v u then 1 else 0 := Finset.sum_comm
        _ = ∑ u ∈ U, (blueNbhdR u).card := by
              refine Finset.sum_congr rfl fun u _ => ?_
              dsimp [blueNbhdR]; rw [Finset.card_filter]
              refine Finset.sum_congr rfl fun v _ => ?_
              by_cases h : Gᶜ.Adj v u
              · simp [h, (Gᶜ.adj_comm _ _).1 h]
              · have h' : ¬ Gᶜ.Adj u v := fun huv => h ((Gᶜ.adj_comm _ _).1 huv)
                simp [h, h']
    -- Apply Jensen's inequality to fallFactPos b
    have hjensen : (R.card : ℝ) * fallFactPos b (σ * (m : ℝ)) ≤
        (b.factorial : ℝ) * (∑ v ∈ R, (Nat.choose (blueNbhdU v).card b : ℝ)) := by
      have hconv := convexOn_fallFactPos b hb
      have hw_sum : ∑ _v ∈ R, ((R.card : ℝ)⁻¹) = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hR_pos.ne']
      have havg : ∑ v ∈ R, (R.card : ℝ)⁻¹ • ((blueNbhdU v).card : ℝ) = σ * (m : ℝ) := by
        simp only [smul_eq_mul, ← Finset.mul_sum]
        have hsum_r : ∑ v ∈ R, ((blueNbhdU v).card : ℝ) = (eB : ℝ) := by
          exact_mod_cast hsum_degU
        rw [hsum_r]
        dsimp [σ]; field_simp [hm_pos.ne', hR_pos.ne']
      have hj := hconv.map_sum_le (t := R) (w := fun _ => (R.card : ℝ)⁻¹)
        (p := fun v => ((blueNbhdU v).card : ℝ))
        (fun _ _ => inv_nonneg.2 hR_pos.le) hw_sum (fun _ _ => Set.mem_univ _)
      rw [havg] at hj
      simp only [smul_eq_mul, ← Finset.mul_sum] at hj
      have hmul := mul_le_mul_of_nonneg_left hj hR_pos.le
      rw [← mul_assoc, mul_inv_cancel₀ hR_pos.ne', one_mul] at hmul
      calc (R.card : ℝ) * fallFactPos b (σ * (m : ℝ))
          ≤ ∑ v ∈ R, fallFactPos b ((blueNbhdU v).card : ℝ) := hmul
        _ = ∑ v ∈ R, (b.factorial : ℝ) * (Nat.choose (blueNbhdU v).card b : ℝ) :=
            Finset.sum_congr rfl fun v _ => fallFactPos_nat b _
        _ = (b.factorial : ℝ) * ∑ v ∈ R, (Nat.choose (blueNbhdU v).card b : ℝ) := by
            rw [Finset.mul_sum]
    -- Lower bound fallFactPos b (σ * m)
    have hff_lb : σ ^ b * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ)) ≤
        fallFactPos b (σ * (m : ℝ)) := by
      have hge : (b : ℝ) - 1 ≤ σ * (m : ℝ) := by linarith
      have hff_eq : fallFactPos b (σ * (m : ℝ)) = ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := by
        unfold fallFactPos; rw [if_pos hge]
      have hff_m : (b.factorial : ℝ) * (Nat.choose m b : ℝ) =
          ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)) := by
        rw [← fallFactPos_nat b m]
        unfold fallFactPos
        have : (b : ℝ) - 1 ≤ (m : ℝ) := by
          have : (b : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb_le_m
          linarith
        rw [if_pos this]
      rw [hff_eq, hff_m]
      have hfrac : (b : ℝ) ^ 2 / (σ * (m : ℝ)) ≤ 1 / 5 := by
        rw [div_le_iff₀ (mul_pos hσ0 hm_pos)]
        have h1 : μ * (m : ℝ) ≥ 10 * (b : ℝ) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hm_ge hμ0.le
          have heq : μ * (10 * μ⁻¹ * (b : ℝ) ^ 2) = 10 * (b : ℝ) ^ 2 := by
            field_simp [hμ0.ne']
          linarith
        nlinarith
      have h1 := fallFact_mul_ge hσ0 hσ1 hb hbm_cond
      have hnn_prod : 0 ≤ ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)) := by
        rw [← hff_m]; positivity
      calc σ ^ b * (4 / 5) * (∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)))
          ≤ σ ^ b * (1 - (b : ℝ) ^ 2 / (σ * (m : ℝ))) * (∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ hnn_prod
            exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hσ0.le _)
        _ ≤ ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := h1
    -- Combine bounds: (4/5)^3 = 64/125 ≥ 1/2
    have hσ_pow : μ ^ b * (4 / 5) ≤ σ ^ b := by
      have hbern : (4 / 5 : ℝ) ≤ (1 - 1 / (5 * (b : ℝ))) ^ b := by
        have hneg : (-2 : ℝ) ≤ -(1 / (5 * (b : ℝ))) := by
          have : 1 / (5 * (b : ℝ)) ≤ 1 / 5 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          linarith
        have h1 := one_add_mul_le_pow hneg b
        have heq1 : 1 + (b : ℝ) * -(1 / (5 * (b : ℝ))) = 4 / 5 := by
          field_simp [hb_pos.ne']; ring
        have heq2 : 1 + -(1 / (5 * (b : ℝ))) = 1 - 1 / (5 * (b : ℝ)) := by ring
        rw [heq1, heq2] at h1
        exact h1
      have hpow1 : (μ * (1 - 1 / (5 * (b : ℝ)))) ^ b ≤ σ ^ b := by
        apply pow_le_pow_left₀ _ hσ_lb1
        have : 1 / (5 * (b : ℝ)) ≤ 1 / 5 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        nlinarith
      rw [mul_pow] at hpow1
      exact (mul_le_mul_of_nonneg_left hbern (pow_nonneg hμ0.le _)).trans hpow1
    have hR_lb : (4 / 5 : ℝ) * (X.card : ℝ) ≤ (R.card : ℝ) := by
      have h1 : (5 : ℝ) * (m : ℝ) ≤ (X.card : ℝ) := by
        nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]
      have h2 : (R.card : ℝ) + (m : ℝ) = (X.card : ℝ) := by exact_mod_cast hRcard
      linarith
    have hsum_T_lb : (Nat.choose m b : ℝ) * (μ ^ b / 2 * (X.card : ℝ)) ≤
        ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ) := by
      have hfac_pos : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
      have hdouble_r : ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ) =
          ∑ v ∈ R, (Nat.choose (blueNbhdU v).card b : ℝ) := by
        rw [← Nat.cast_sum, ← Nat.cast_sum, hdouble_T]
      rw [hdouble_r]
      suffices h : (b.factorial : ℝ) * ((Nat.choose m b : ℝ) * (μ ^ b / 2 * (X.card : ℝ))) ≤
          (b.factorial : ℝ) * ∑ v ∈ R, (Nat.choose (blueNbhdU v).card b : ℝ) by
        exact le_of_mul_le_mul_left h hfac_pos
      have h1 : (R.card : ℝ) * (σ ^ b * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ))) ≤
          (R.card : ℝ) * fallFactPos b (σ * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hff_lb hR_pos.le
      have h2 : (4 / 5 : ℝ) * (X.card : ℝ) * (μ ^ b * (4 / 5) * (4 / 5) *
          ((b.factorial : ℝ) * (Nat.choose m b : ℝ))) ≤
          (R.card : ℝ) * (σ ^ b * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ))) := by
        have hb' : μ ^ b * (4 / 5) * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ)) ≤
            σ ^ b * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hσ_pow (by norm_num)
        exact mul_le_mul hR_lb hb' (by positivity) hR_pos.le
      have h3 : (b.factorial : ℝ) * ((Nat.choose m b : ℝ) * (μ ^ b / 2 * (X.card : ℝ))) ≤
          (4 / 5 : ℝ) * (X.card : ℝ) * (μ ^ b * (4 / 5) * (4 / 5) *
          ((b.factorial : ℝ) * (Nat.choose m b : ℝ))) := by
        have hconst : (1 / 2 : ℝ) ≤ (4 / 5) * (4 / 5) * (4 / 5) := by norm_num
        have hnn : 0 ≤ (b.factorial : ℝ) * (Nat.choose m b : ℝ) * μ ^ b * (X.card : ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hconst hnn
        have hL : (b.factorial : ℝ) * (Nat.choose m b : ℝ) * μ ^ b * (X.card : ℝ) * (1 / 2) =
            (b.factorial : ℝ) * ((Nat.choose m b : ℝ) * (μ ^ b / 2 * (X.card : ℝ))) := by ring
        have hR : (b.factorial : ℝ) * (Nat.choose m b : ℝ) * μ ^ b * (X.card : ℝ) * ((4 / 5) * (4 / 5) * (4 / 5)) =
            (4 / 5 : ℝ) * (X.card : ℝ) * (μ ^ b * (4 / 5) * (4 / 5) * ((b.factorial : ℝ) * (Nat.choose m b : ℝ))) := by ring
        rwa [hL, hR] at hmul
      exact h3.trans (h2.trans (h1.trans hjensen))
    -- Pick S ∈ U.powersetCard b with |Tset S| ≥ μ^b / 2 * |X|
    have hpc_card : (U.powersetCard b).card = Nat.choose m b := by
      rw [Finset.card_powersetCard, hUcard]
    have hpc_ne : (U.powersetCard b).Nonempty :=
      Finset.card_pos.1 (hpc_card ▸ Nat.choose_pos hb_le_m)
    obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (U.powersetCard b) (fun S => (Tset S).card) hpc_ne
    have hST : μ ^ b / 2 * (X.card : ℝ) ≤ ((Tset S).card : ℝ) := by
      have hsum_ub : ∑ S' ∈ U.powersetCard b, ((Tset S').card : ℝ) ≤
          ((U.powersetCard b).card : ℝ) * ((Tset S).card : ℝ) := by
        calc ∑ S' ∈ U.powersetCard b, ((Tset S').card : ℝ)
            ≤ ∑ _S' ∈ U.powersetCard b, ((Tset S).card : ℝ) :=
              Finset.sum_le_sum fun S' hS' => by exact_mod_cast hSmax S' hS'
          _ = ((U.powersetCard b).card : ℝ) * ((Tset S).card : ℝ) := by simp
      rw [hpc_card] at hsum_ub
      have hch_pos : (0 : ℝ) < (Nat.choose m b : ℝ) := by
        exact_mod_cast Nat.choose_pos hb_le_m
      exact le_of_mul_le_mul_left (hsum_T_lb.trans hsum_ub) hch_pos
    rcases Finset.mem_powersetCard.1 hSmem with ⟨hSU, hScard⟩
    refine ⟨S, Tset S, hSU.trans hUX, (Finset.filter_subset _ R).trans hRsub,
      Disjoint.mono hSU (Finset.filter_subset _ R) hdisjUR,
      ⟨hUcl.1.subset hSU, hScard⟩,
      fun u hu v hv => (Finset.mem_filter.1 hv).2 u hu, hST⟩

end BlueBook

end Erdos627AFM

/- ==================== Section: BookMain.lean ====================-/
namespace Erdos627AFM

open SimpleGraph Finset Real Set Filter Topology

/-- Lemma 11 in GNNW: limit of (p^(1/r) - μ)^r * (1 - μ)^(1 - r) as r → ∞
equals p^(1 / (1 - μ)) * (1 - μ). We only need existence of large r > 1. -/
lemma exists_r_of_lt_limit {p μ x₀ : ℝ} (hp0 : 0 < p) (_hp1 : p < 1)
    (_hμ0 : 0 < μ) (hμ1 : μ < 1) (hx : x₀ < p ^ (1 / (1 - μ)) * (1 - μ)) :
    ∃ r : ℝ, 1 < r ∧ μ < p ^ (1 / r) ∧ x₀ < (p ^ (1 / r) - μ) ^ r * (1 - μ) ^ (1 - r) := by
  have h1μ : 0 < 1 - μ := sub_pos.2 hμ1
  -- Consider f(t) = log ((p^t - μ) / (1 - μ)) near t = 0
  let g : ℝ → ℝ := fun t => (Real.exp (t * Real.log p) - μ) / (1 - μ)
  have hg0 : g 0 = 1 := by simp [g, div_self h1μ.ne']
  have hgd : HasDerivAt g (Real.log p / (1 - μ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log p) (Real.log p) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Real.log p)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * Real.log p)) (Real.exp (0 * Real.log p) * Real.log p) 0 :=
      h1.exp
    simp only [zero_mul, Real.exp_zero, one_mul] at h2
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (t * Real.log p) - μ) (Real.log p) 0 :=
      h2.sub_const μ
    exact h3.div_const (1 - μ)
  have hlog_d : HasDerivAt (fun t => Real.log (g t)) (Real.log p / (1 - μ)) 0 := by
    have h := hgd.log (by rw [hg0]; exact one_ne_zero)
    simpa [hg0] using h
  -- Therefore (log (g t)) / t → log p / (1 - μ) as t → 0
  have hslope : Tendsto (fun t : ℝ => Real.log (g t) / t) (𝓝[≠] 0) (𝓝 (Real.log p / (1 - μ))) := by
    have h := hasDerivAt_iff_tendsto_slope.1 hlog_d
    refine h.congr' (Eventually.of_forall fun t => ?_)
    simp [slope_def_field, hg0, Real.log_one]
  -- Pull back along t = 1 / r as r → ∞
  have hinv_tendsto : Tendsto (fun r : ℝ => (1 : ℝ) / r) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (div_pos one_pos hr).ne'
  have hlim_log : Tendsto (fun r : ℝ => r * Real.log (g (1 / r))) atTop (𝓝 (Real.log p / (1 - μ))) := by
    have hcomp := hslope.comp hinv_tendsto
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Function.comp_apply, one_div, div_inv_eq_mul, mul_comm]
  have hlim_exp : Tendsto (fun r : ℝ => Real.exp (r * Real.log (g (1 / r))) * (1 - μ))
      atTop (𝓝 (p ^ (1 / (1 - μ)) * (1 - μ))) := by
    have h1 := (Real.continuous_exp.tendsto _).comp hlim_log |>.mul_const (1 - μ)
    have hval : Real.exp (Real.log p / (1 - μ)) * (1 - μ) = p ^ (1 / (1 - μ)) * (1 - μ) := by
      rw [Real.rpow_def_of_pos hp0]
      ring_nf
    simpa [hval] using h1
  -- Also p^(1/r) → 1 > μ as r → ∞
  have hp_tendsto : Tendsto (fun r : ℝ => p ^ (1 / r)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => Real.exp ((1 / r) * Real.log p)) atTop (𝓝 (Real.exp 0)) := by
      apply (Real.continuous_exp.tendsto _).comp
      have := (tendsto_const_nhds (x := (1 : ℝ)).div_atTop tendsto_id).mul_const (Real.log p)
      simpa using this
    rw [Real.exp_zero] at h1
    refine h1.congr' (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos hp0, mul_comm]
  have hev1 := hlim_exp.eventually (Ioi_mem_nhds hx)
  have hev2 := hp_tendsto.eventually (Ioi_mem_nhds hμ1)
  have hev3 := eventually_gt_atTop (1 : ℝ)
  obtain ⟨r, hr1, hr2, hr3⟩ := (hev1.and (hev2.and hev3)).exists
  refine ⟨r, hr3, hr2, ?_⟩
  have hdiff_pos : 0 < p ^ (1 / r) - μ := sub_pos.2 hr2
  have hg_pos : 0 < g (1 / r) := by
    dsimp [g]
    have hp_eq : Real.exp ((1 / r) * Real.log p) = p ^ (1 / r) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    rw [hp_eq]
    exact div_pos hdiff_pos h1μ
  have heq : Real.exp (r * Real.log (g (1 / r))) * (1 - μ) =
      (p ^ (1 / r) - μ) ^ r * (1 - μ) ^ (1 - r) := by
    have hp_eq : Real.exp ((1 / r) * Real.log p) = p ^ (1 / r) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    have hg_eq : g (1 / r) = (p ^ (1 / r) - μ) / (1 - μ) := by dsimp [g]; rw [hp_eq]
    conv_lhs => rw [← Real.exp_log h1μ]
    rw [← Real.exp_add, Real.rpow_def_of_pos hdiff_pos,
        Real.rpow_def_of_pos h1μ, ← Real.exp_add]
    congr 1
    rw [hg_eq, Real.log_div hdiff_pos.ne' h1μ.ne']
    ring
  rw [← heq]
  exact hr1

/-- Growth helper: for any c > 0 and A, B ≥ 0, eventually n^A * exp(B * (log n)^3) ≤ exp(c * n). -/
lemma eventually_poly_exp_log_cube_le_exp (c : ℝ) (hc : 0 < c) (A B : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ A * Real.exp (B * (Real.log (n : ℝ)) ^ 3) ≤ Real.exp (c * (n : ℝ)) := by
  have hlog : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 4)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hpow3 : (fun x : ℝ => (Real.log x) ^ 3) =o[atTop] (fun x : ℝ => x) := by
    have h1 := hlog.bound (show (0 : ℝ) < 1 by norm_num)
    rw [Asymptotics.isLittleO_iff]
    intro d hd
    have h2 : ∀ᶠ x : ℝ in atTop, x ^ ((3 : ℝ) / 4) ≤ d * x := by
      filter_upwards [eventually_gt_atTop (max 1 (d⁻¹ ^ 4))] with x hx
      have hx1 : 1 < x := (le_max_left _ _).trans_lt hx
      have hxd : d⁻¹ ^ 4 < x := (le_max_right _ _).trans_lt hx
      have hx0 : 0 < x := by linarith
      have h14 : d⁻¹ ≤ x ^ ((1 : ℝ) / 4) := by
        have hpow := Real.rpow_le_rpow (by positivity) hxd.le (show (0 : ℝ) ≤ 1 / 4 by norm_num)
        rw [← Real.rpow_natCast d⁻¹ 4, ← Real.rpow_mul (by positivity)] at hpow
        norm_num at hpow
        exact hpow
      have hmul := mul_le_mul_of_nonneg_right h14 (mul_nonneg hd.le (Real.rpow_nonneg hx0.le ((3 : ℝ) / 4)))
      have hcancel : d⁻¹ * (d * x ^ ((3 : ℝ) / 4)) = x ^ ((3 : ℝ) / 4) := by field_simp [hd.ne']
      have hadd : x ^ ((1 : ℝ) / 4) * (d * x ^ ((3 : ℝ) / 4)) = d * x := by
        calc x ^ ((1 : ℝ) / 4) * (d * x ^ ((3 : ℝ) / 4))
            = d * (x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4)) := by ring
          _ = d * x ^ ((1 : ℝ) / 4 + (3 : ℝ) / 4) := by rw [← Real.rpow_add hx0]
          _ = d * x := by norm_num
      linarith
    filter_upwards [h1, h2, eventually_gt_atTop (1 : ℝ)] with x hx1 hx2 hxgt
    have hx0 : 0 < x := by linarith
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hxgt.le
    rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx1
    rw [Real.norm_of_nonneg (pow_nonneg hlognn 3), Real.norm_of_nonneg hx0.le]
    have hcube : (Real.log x) ^ 3 ≤ x ^ ((3 : ℝ) / 4) := by
      calc (Real.log x) ^ 3 ≤ (x ^ ((1 : ℝ) / 4)) ^ 3 := pow_le_pow_left₀ hlognn hx1 3
        _ = (x ^ ((1 : ℝ) / 4)) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast (x ^ ((1 : ℝ) / 4)) 3).symm
        _ = x ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_mul hx0.le]; norm_num
    exact hcube.trans hx2
  have hlog1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) := by
    simpa using isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
  have hA : ∀ᶠ x : ℝ in atTop, |A| * Real.log x ≤ (c / 2) * x := by
    by_cases hA0 : |A| = 0
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [hA0, zero_mul]; positivity
    · have hAp : 0 < |A| := lt_of_le_of_ne (abs_nonneg A) (Ne.symm hA0)
      filter_upwards [hlog1.bound (div_pos (half_pos hc) hAp), eventually_gt_atTop (1 : ℝ)] with x hx hxgt
      have hlognn : 0 ≤ Real.log x := Real.log_nonneg hxgt.le
      rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg (by linarith)] at hx
      calc |A| * Real.log x ≤ |A| * (c / 2 / |A| * x) := mul_le_mul_of_nonneg_left hx hAp.le
        _ = (c / 2) * x := by field_simp [hAp.ne']
  have hB : ∀ᶠ x : ℝ in atTop, |B| * (Real.log x) ^ 3 ≤ (c / 2) * x := by
    by_cases hB0 : |B| = 0
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [hB0, zero_mul]; positivity
    · have hBp : 0 < |B| := lt_of_le_of_ne (abs_nonneg B) (Ne.symm hB0)
      filter_upwards [hpow3.bound (div_pos (half_pos hc) hBp), eventually_gt_atTop (1 : ℝ)] with x hx hxgt
      have hlognn : 0 ≤ Real.log x := Real.log_nonneg hxgt.le
      rw [Real.norm_of_nonneg (pow_nonneg hlognn 3), Real.norm_of_nonneg (by linarith)] at hx
      calc |B| * (Real.log x) ^ 3 ≤ |B| * (c / 2 / |B| * x) := mul_le_mul_of_nonneg_left hx hBp.le
        _ = (c / 2) * x := by field_simp [hBp.ne']
  have hev : ∀ᶠ n : ℕ in atTop,
      |A| * Real.log (n : ℝ) ≤ (c / 2) * (n : ℝ) ∧
      |B| * (Real.log (n : ℝ)) ^ 3 ≤ (c / 2) * (n : ℝ) ∧
      (1 : ℝ) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (hA.and (hB.and (eventually_gt_atTop (1 : ℝ))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hAn, hBn, hngt⟩ := hN n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlognn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hngt.le
  rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : Real.log (n : ℝ) * A ≤ |A| * Real.log (n : ℝ) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self A) hlognn
  have h2 : B * (Real.log (n : ℝ)) ^ 3 ≤ |B| * (Real.log (n : ℝ)) ^ 3 :=
    mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg hlognn 3)
  linarith

/-- Monotonicity of t ↦ x^(1/r) (1 - t)^(1 - 1/r) + μ^(1/r) t^(1 - 1/r) on [0, μ/(μ+x)]. -/
lemma rpow_sum_le_of_le {x μ r u₁ u₂ : ℝ} (hx : 0 < x) (hμ : 0 < μ) (hr : 1 < r)
    (h0 : 0 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ μ / (μ + x)) (h2lt1 : u₂ < 1) :
    x ^ (1 / r) * (1 - u₁) ^ (1 - 1 / r) + μ ^ (1 / r) * u₁ ^ (1 - 1 / r) ≤
      x ^ (1 / r) * (1 - u₂) ^ (1 - 1 / r) + μ ^ (1 / r) * u₂ ^ (1 - 1 / r) := by
  let f : ℝ → ℝ := fun t => x ^ (1 / r) * (1 - t) ^ (1 - 1 / r) + μ ^ (1 / r) * t ^ (1 - 1 / r)
  have hpos_exp : 0 < 1 - 1 / r := by
    have : 1 / r < 1 := (div_lt_one (by linarith)).2 hr
    linarith
  have hcont : ContinuousOn f (Icc u₁ u₂) := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact (continuousOn_const.sub continuousOn_id).rpow_const fun t _ => Or.inr hpos_exp.le
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_id.rpow_const fun t _ => Or.inr hpos_exp.le
  have hderiv : ∀ t ∈ Ioo u₁ u₂,
      HasDerivAt f ((1 - 1 / r) * (μ ^ (1 / r) * t ^ (-(1 / r)) -
        x ^ (1 / r) * (1 - t) ^ (-(1 / r)))) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt h0 ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun s => (1 - s) ^ (1 - 1 / r))
        ((1 - 1 / r) * (1 - t) ^ ((1 - 1 / r) - 1) * (-1)) t := by
      have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
        ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).congr_deriv (by norm_num)
      exact (hsub.rpow_const (p := 1 - 1 / r) (Or.inl ht1.ne')).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun s => s ^ (1 - 1 / r))
        ((1 - 1 / r) * t ^ ((1 - 1 / r) - 1)) t :=
      ((hasDerivAt_id t).rpow_const (p := 1 - 1 / r) (Or.inl ht0.ne')).congr_deriv (by simp only [id_eq]; ring)
    have hcomb := (hd1.const_mul (x ^ (1 / r))).fun_add (hd2.const_mul (μ ^ (1 / r)))
    exact hcomb.congr_deriv (by
      have hexp : (1 - 1 / r) - 1 = -(1 / r) := by ring
      rw [hexp]; ring)
  have hmono : MonotoneOn f (Icc u₁ u₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u₁ u₂) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      apply mul_nonneg hpos_exp.le
      apply sub_nonneg.2
      have ht0 : 0 < t := lt_of_le_of_lt h0 ht.1
      have ht1 : 0 < 1 - t := by linarith [ht.2]
      have ht_le : t ≤ μ / (μ + x) := ht.2.le.trans h2
      have hcross : t * (μ + x) ≤ μ := (le_div_iff₀ (by positivity)).1 ht_le
      have hratio : x / (1 - t) ≤ μ / t := by
        rw [div_le_div_iff₀ ht1 ht0]; nlinarith
      have hrpos : 0 < 1 / r := div_pos one_pos (by linarith)
      have hrpow := Real.rpow_le_rpow (div_nonneg hx.le ht1.le) hratio hrpos.le
      rw [Real.div_rpow hx.le ht1.le, Real.div_rpow hμ.le ht0.le] at hrpow
      rw [Real.rpow_neg ht1.le, Real.rpow_neg ht0.le]
      simpa only [div_eq_mul_inv] using hrpow
  exact hmono (left_mem_Icc.2 h12) (right_mem_Icc.2 h12) h12

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3200000 in
/-- Lemma 12 in GNNW (the main inductive theorem replacing the book algorithm). -/
lemma book_main {μ₀ x₀ y₀ p : ℝ}
    (hμ0 : 0 < μ₀) (hμ1 : μ₀ < 1)
    (hx0 : 0 < x₀) (hx1 : x₀ < 1)
    (hy0 : 0 < y₀) (hy1 : y₀ < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hxp : x₀ < p ^ (1 / (1 - μ₀)) * (1 - μ₀))
    (hR : ∃ x₁ y₁ : ℝ, x₀ < x₁ ∧ y₀ < y₁ ∧ InR x₁ y₁) :
    ∃ L₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (k l t : ℕ), 1 ≤ k → L₀ ≤ l → 1 ≤ t →
      ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y →
      p ≤ dens G X Y →
      (x₀ ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ₀ ^ t)⁻¹ ≤ (X.card : ℝ) * (Y.card : ℝ) →
      IsGood G k l t X Y := by
  -- Step 1: Choose r > 1 and ε > 0 satisfying all strict room inequalities (e:xx)
  obtain ⟨r, hr1, hμ_lt_pr, hx_lt_r⟩ := exists_r_of_lt_limit hp0 hp1 hμ0 hμ1 hxp
  have hr0 : 0 < r := by linarith
  obtain ⟨xR, yR, hx₀_lt_xR, hy₀_lt_yR, hInR⟩ := hR
  have hx₀μ₀_lt1 : x₀ + μ₀ < 1 := by
    have hpr_lt1 : p ^ (1 / r) < 1 := Real.rpow_lt_one hp0.le hp1 (div_pos one_pos hr0)
    have h1 : (p ^ (1 / r) - μ₀) ^ r * (1 - μ₀) ^ (1 - r) < 1 - μ₀ := by
      have hbase : (p ^ (1 / r) - μ₀) / (1 - μ₀) < 1 :=
        (div_lt_one (sub_pos.2 hμ1)).2 (by linarith)
      have hbase0 : 0 < (p ^ (1 / r) - μ₀) / (1 - μ₀) :=
        div_pos (sub_pos.2 hμ_lt_pr) (sub_pos.2 hμ1)
      have hpow : ((p ^ (1 / r) - μ₀) / (1 - μ₀)) ^ r < 1 :=
        Real.rpow_lt_one hbase0.le hbase hr0
      have heq : (p ^ (1 / r) - μ₀) ^ r * (1 - μ₀) ^ (1 - r) =
          ((p ^ (1 / r) - μ₀) / (1 - μ₀)) ^ r * (1 - μ₀) := by
        rw [Real.div_rpow (sub_pos.2 hμ_lt_pr).le (sub_pos.2 hμ1).le,
            Real.rpow_sub (sub_pos.2 hμ1), Real.rpow_one]
        ring
      rw [heq]; nlinarith [sub_pos.2 hμ1]
    linarith
  -- Choose ε > 0 via continuity at 0
  have hcont_rhs : ContinuousAt (fun e : ℝ =>
      ((p - e) ^ (1 / r) - μ₀ - 3 * e) ^ r * (1 - μ₀ - e) ^ (1 - r) - e) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => (p - e) ^ (1 / r)) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simp [hp0.ne']))
    have h2 : ContinuousAt (fun e : ℝ => (p - e) ^ (1 / r) - μ₀ - 3 * e) 0 :=
      (h1.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)
    have h2pos : (p - 0) ^ (1 / r) - μ₀ - 3 * 0 ≠ 0 := by
      simp only [sub_zero, mul_zero]; exact (sub_pos.2 hμ_lt_pr).ne'
    have h3 : ContinuousAt (fun e : ℝ => ((p - e) ^ (1 / r) - μ₀ - 3 * e) ^ r) 0 :=
      h2.rpow_const (Or.inl h2pos)
    have h4 : ContinuousAt (fun e : ℝ => (1 - μ₀ - e) ^ (1 - r)) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simp [(sub_pos.2 hμ1).ne']))
    exact (h3.mul h4).sub continuousAt_id
  have hcont_pr : ContinuousAt (fun e : ℝ => (p - e) ^ (1 / r) - (μ₀ + 3 * e)) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => (p - e) ^ (1 / r)) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simp [hp0.ne']))
    exact h1.sub (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
  have hcont_frac : ContinuousAt (fun e : ℝ => μ₀ / (μ₀ + 2 * e + x₀) - (μ₀ + 2 * e)) 0 := by
    have hden : μ₀ + 2 * (0 : ℝ) + x₀ ≠ 0 := by linarith
    exact (continuousAt_const.div
      ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).add continuousAt_const)
      hden).sub (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
  have hfrac0 : 0 < μ₀ / (μ₀ + 2 * (0 : ℝ) + x₀) - (μ₀ + 2 * (0 : ℝ)) := by
    simp only [mul_zero, add_zero]
    rw [sub_pos, lt_div_iff₀ (by linarith)]
    nlinarith
  have hpr0 : 0 < (p - (0 : ℝ)) ^ (1 / r) - (μ₀ + 3 * (0 : ℝ)) := by
    simp only [sub_zero, mul_zero, add_zero]; linarith
  have hrhs0 : x₀ < ((p - (0 : ℝ)) ^ (1 / r) - μ₀ - 3 * (0 : ℝ)) ^ r *
      (1 - μ₀ - (0 : ℝ)) ^ (1 - r) - (0 : ℝ) := by
    simpa using hx_lt_r
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.1 hcont_rhs
    (((p - 0) ^ (1 / r) - μ₀ - 3 * 0) ^ r * (1 - μ₀ - 0) ^ (1 - r) - 0 - x₀) (sub_pos.2 hrhs0)
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.1 hcont_pr
    ((p - 0) ^ (1 / r) - (μ₀ + 3 * 0)) hpr0
  obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ := Metric.continuousAt_iff.1 hcont_frac
    (μ₀ / (μ₀ + 2 * 0 + x₀) - (μ₀ + 2 * 0)) hfrac0
  -- Choose ε > 0 smaller than all constraints
  let ε : ℝ := min (min (min (δ₁ / 2) (δ₂ / 2)) (min (δ₃ / 2) (p / 4)))
    (min (min ((1 - μ₀ - x₀) / 4) ((xR - x₀) / 4))
      (min ((yR - y₀) / 4) (min ((1 - μ₀) / 4) ((1 - y₀) / 4))))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have : 0 < 1 - μ₀ - x₀ := by linarith
    have : 0 < xR - x₀ := by linarith
    have : 0 < yR - y₀ := by linarith
    have : 0 < 1 - μ₀ := by linarith
    have : 0 < 1 - y₀ := by linarith
    positivity
  have hε_δ₁ : ε < δ₁ := by
    have : ε ≤ δ₁ / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hε_δ₂ : ε < δ₂ := by
    have : ε ≤ δ₂ / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hε_δ₃ : ε < δ₃ := by
    have : ε ≤ δ₃ / 2 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hε_p : 4 * ε ≤ p := by
    have : ε ≤ p / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hε_sum : μ₀ + x₀ + 4 * ε ≤ 1 := by
    have : ε ≤ (1 - μ₀ - x₀) / 4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hε_xR : x₀ + 3 * ε < xR := by
    have : ε ≤ (xR - x₀) / 4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hε_yR : y₀ + 3 * ε < yR := by
    have : ε ≤ (yR - y₀) / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hε_μ1 : μ₀ + 4 * ε ≤ 1 := by
    have : ε ≤ (1 - μ₀) / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hε_y1 : y₀ + 4 * ε ≤ 1 := by
    have : ε ≤ (1 - y₀) / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hε_rhs : x₀ < ((p - ε) ^ (1 / r) - μ₀ - 3 * ε) ^ r * (1 - μ₀ - ε) ^ (1 - r) - ε := by
    have hdist : dist ε 0 < δ₁ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; exact hε_δ₁
    have h := hδ₁ hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith
  have hε_pr : μ₀ + 3 * ε < (p - ε) ^ (1 / r) := by
    have hdist : dist ε 0 < δ₂ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; exact hε_δ₂
    have h := hδ₂ hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith
  have hε_frac : μ₀ + 2 * ε < μ₀ / (μ₀ + 2 * ε + x₀) := by
    have hdist : dist ε 0 < δ₃ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; exact hε_δ₃
    have h := hδ₃ hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith
  -- Set x = x₀ + ε, y = y₀ + ε, μ = μ₀ + ε
  let x : ℝ := x₀ + ε
  let y : ℝ := y₀ + ε
  let μ : ℝ := μ₀ + ε
  have hx_pos : 0 < x := by dsimp [x]; linarith
  have hy_pos : 0 < y := by dsimp [y]; linarith
  have hμ_pos : 0 < μ := by dsimp [μ]; linarith
  have hx_lt1 : x < 1 := by dsimp [x]; linarith
  have hy_lt1 : y < 1 := by dsimp [y]; linarith
  have hμ_lt1 : μ < 1 := by dsimp [μ]; linarith
  have hμ_add_lt1 : μ + ε < 1 := by dsimp [μ]; linarith
  have hx_ratio : (1 + ε) * x₀ ≤ x := by
    dsimp [x]; nlinarith
  have hy_ratio : (1 + ε) * y₀ ≤ y := by
    dsimp [y]; nlinarith
  have hμ_ratio : (1 + ε) * μ₀ ≤ μ := by
    dsimp [μ]; nlinarith
  have hx_ratio2 : (1 + ε) * x ≤ x + ε := by
    dsimp [x]; nlinarith
  have hy_ratio2 : (1 + ε) * y ≤ y + ε := by
    dsimp [y]; nlinarith
  -- Use InR xR yR at (x + ε, y + ε) = (x₀ + 2ε, y₀ + 2ε)
  obtain ⟨N_R, hN_R⟩ := hInR.2.2.2.2 (x + ε) (by dsimp [x]; linarith) (by dsimp [x]; linarith)
    (y + ε) (by dsimp [y]; linarith) (by dsimp [y]; linarith)
  -- Choose L₀ large enough for all asymptotic inequalities
  have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  -- Constants for b, m, w bounds in terms of n = k + l + t:
  -- b = ⌈(2r log(k+t) - r log ε + log 2) / log(1+ε)⌉₊
  -- Note for n = k + l + t ≥ 4, k + t ≤ n, log(k+t) ≤ log n
  let C_b : ℝ := (2 * r + |(-r * Real.log ε + Real.log 2)| + 2) / Real.log (1 + ε)
  have hCb_pos : 0 < C_b := by
    dsimp [C_b]
    apply div_pos _ hlog1ε
    have : 0 ≤ |(-r * Real.log ε + Real.log 2)| := abs_nonneg _
    linarith
  let C_m : ℝ := 10 * μ⁻¹ * C_b ^ 2 + 2
  have hCm_pos : 0 < C_m := by dsimp [C_m]; positivity
  -- We need for all n = k + l + t ≥ L₀:
  -- (1) (n^r / ε^r) ≤ (1 + ε)^n  (for base step (e:moment) from (e:bookmain))
  -- (2) n^2 / (ε * (1 + ε)^n) ≤ ε  (for final step (e:moment4))
  -- (3) 5 * (C_m * (log n)^2)^2 ≤ (1 + ε)^n  (for |X| ≥ 5 m^2)
  -- (4) n^3 * exp((C_m * (log n)^2) * (2 * log n)) ≤ ε * (p - ε) * (1 + ε)^n  (for w ≤ ε(p-ε)/(k+t)^3 * |X|)
  -- (5) C_m * (log n)^2 ≤ n  (so k + m ≤ 2 n ≤ n^2)
  -- All of these are implied by n^A * exp(B * (log n)^3) ≤ exp(c * n) with c = log(1+ε)/2!
  let A_big : ℝ := max r 3 + 4
  let B_big : ℝ := 2 * C_m + 1
  obtain ⟨N₁, hN₁⟩ := eventually_poly_exp_log_cube_le_exp (Real.log (1 + ε) / 2) (half_pos hlog1ε) A_big B_big
  let K_const : ℝ := max (max (ε⁻¹ ^ r) (ε⁻¹ ^ 2)) (max (5 * C_m ^ 2) ((ε * (p - ε))⁻¹)) + 1
  have hK_pos : 0 < K_const := by dsimp [K_const]; positivity
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * Real.log K_const / Real.log (1 + ε))
  have hCm_small : ∃ N₄ : ℕ, ∀ n : ℕ, N₄ ≤ n → C_m * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hlog := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have hc : 0 < 1 / Real.sqrt C_m := by positivity
    have hev := tendsto_natCast_atTop_atTop.eventually ((hlog.bound hc).and (eventually_gt_atTop (1 : ℝ)))
    obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 hev
    refine ⟨N₄, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN₄ n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlognn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h2.le
    rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] at h1
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (1 / Real.sqrt C_m * (n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ hlognn h1 2
    have hrhs : (1 / Real.sqrt C_m * (n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (n : ℝ) / C_m := by
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hCm_pos.le, ← Real.rpow_natCast ((n : ℝ) ^ _),
          ← Real.rpow_mul hn0.le]
      norm_num; ring
    rw [hrhs, le_div_iff₀ hCm_pos] at hsq
    linarith
  obtain ⟨N₄, hN₄⟩ := hCm_small
  let L₀ : ℕ := max (max (max N₁ N₂) (max N₄ N_R)) 4
  have hL₀_pow : ∀ n : ℕ, L₀ ≤ n →
      K_const * ((n : ℝ) ^ A_big * Real.exp (B_big * (Real.log (n : ℝ)) ^ 3)) ≤ (1 + ε) ^ n := by
    intro n hn
    have hn1 : N₁ ≤ n := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hn
    have hn2 : N₂ ≤ n := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hn
    have h1 := hN₁ n hn1
    have h2 : K_const ≤ Real.exp (Real.log (1 + ε) / 2 * (n : ℝ)) := by
      have hlt : 2 * Real.log K_const / Real.log (1 + ε) < (n : ℝ) :=
        hN₂.trans_le (by exact_mod_cast hn2)
      have hmul : Real.log K_const < Real.log (1 + ε) / 2 * (n : ℝ) := by
        have := (div_lt_iff₀ hlog1ε).1 hlt
        linarith
      exact (Real.exp_log hK_pos).symm.trans_le (Real.exp_le_exp.2 hmul.le)
    have heq : (1 + ε) ^ n = Real.exp (Real.log (1 + ε) / 2 * (n : ℝ)) *
        Real.exp (Real.log (1 + ε) / 2 * (n : ℝ)) := by
      rw [← Real.exp_add, show Real.log (1 + ε) / 2 * (n : ℝ) + Real.log (1 + ε) / 2 * (n : ℝ) =
        (n : ℝ) * Real.log (1 + ε) by ring, Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [heq]
    exact mul_le_mul h2 h1 (by positivity) (Real.exp_nonneg _)
  -- Clear dead setup hypotheses so linarith/nlinarith stay fast inside the induction
  clear hcont_rhs hcont_pr hcont_frac hfrac0 hpr0 hrhs0 hδ₁ hδ₂ hδ₃ hδ₁_pos hδ₂_pos hδ₃_pos
    hε_δ₁ hε_δ₂ hε_δ₃ hε_xR hε_yR hInR hx₀_lt_xR hy₀_lt_yR hμ_lt_pr hx_lt_r hxp hx₀μ₀_lt1
    hN₁ hN₂
  -- Helper: (1 + ε)^(k+l+t) bounds needed inside induction
  refine ⟨L₀, fun V _ _ G k l t hk hl ht X Y hXne hYne hdisj hdens hXY => ?_⟩
  classical
  -- Prove stronger inductive claim for fixed l ≥ L₀ by induction on k + t
  have hind : ∀ s : ℕ, ∀ k t : ℕ, k + t = s → 1 ≤ k → 1 ≤ t →
      ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y →
      p - ε / ((k : ℝ) + t) ≤ dens G X Y →
      (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤
        (dens G X Y + ε / ((k : ℝ) + t) - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) →
      IsGood G k l t X Y := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro k t hkt hk ht X Y hXne hYne hdisj hdens_step hmom
      -- Base cases k = 1 or t = 1
      by_cases hk1 : k = 1
      · subst hk1
        left
        obtain ⟨v, hv⟩ := hXne
        exact ⟨{v}, Finset.singleton_subset_iff.2 (Finset.mem_union_left _ hv),
          by simp [SimpleGraph.isNClique_iff]⟩
      by_cases ht1 : t = 1
      · subst ht1
        right; left
        obtain ⟨v, hv⟩ := hXne
        exact ⟨{v}, Finset.singleton_subset_iff.2 hv,
          by simp [SimpleGraph.isNClique_iff]⟩
      have hk2 : 2 ≤ k := by omega
      have ht2 : 2 ≤ t := by omega
      -- Step A (degree regularization): inner induction on X.card
      suffices hreg : ∀ nX : ℕ, ∀ X : Finset V, X.card = nX → X.Nonempty → Disjoint X Y →
          p - ε / ((k : ℝ) + t) ≤ dens G X Y →
          (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤
            (dens G X Y + ε / ((k : ℝ) + t) - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) →
          IsGood G k l t X Y by
        exact hreg X.card X rfl hXne hdisj hdens_step hmom
      intro nX
      induction nX using Nat.strong_induction_on with
      | h nX ihX =>
        intro X hXcard hXne hdisj hdens_step hmom
        set δkt : ℝ := ε / ((k : ℝ) + t)
        have hkt_pos : (0 : ℝ) < (k : ℝ) + t := by positivity
        have hδkt_pos : 0 < δkt := div_pos hε_pos hkt_pos
        have hδkt_le_ε : δkt ≤ ε := by
          dsimp [δkt]; rw [div_le_iff₀ hkt_pos]
          have : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
          nlinarith only [this, hε_pos]
        have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
        have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hXne.card_pos
        have hgap_pos : 0 < dens G X Y + δkt - p := by
          by_contra hle
          have h0 : dens G X Y + δkt - p = 0 := le_antisymm (le_of_not_gt hle) (by linarith)
          rw [h0, Real.zero_rpow hr0.ne', zero_mul] at hmom
          have hpos_lhs : 0 < (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ := by positivity
          linarith
        -- Check degree regularization condition
        by_cases hdeg_all : ∀ v ∈ X, (p - δkt) * (Y.card : ℝ) ≤ ((Y.filter (G.Adj v)).card : ℝ)
        · -- Now all vertices in X have red degree ≥ (p - δkt) |Y| into Y!
          have hdeg_sub : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty → p - δkt ≤ dens G X' Y := by
            intro X' hX'X hX'ne
            have hX'pos : (0 : ℝ) < X'.card := by exact_mod_cast hX'ne.card_pos
            unfold dens
            rw [le_div_iff₀ (mul_pos hX'pos hYpos), redEdges_eq_sum_card_filter]
            have hsum : ∑ _v ∈ X', (p - δkt) * (Y.card : ℝ) ≤
                ∑ v ∈ X', ((Y.filter (G.Adj v)).card : ℝ) :=
              Finset.sum_le_sum fun v hv => hdeg_all v (hX'X hv)
            rw [Finset.sum_const, nsmul_eq_mul] at hsum
            have hcast : ((∑ v ∈ X', (Y.filter (G.Adj v)).card : ℕ) : ℝ) =
                ∑ v ∈ X', ((Y.filter (G.Adj v)).card : ℝ) := by push_cast; rfl
            rw [hcast]; linarith
          -- Step B: Upper bound |Y| via InR, hence lower bound |X| ≥ (1 + ε)^(k + l + t)
          by_cases hYbig : ((x + ε) ^ k)⁻¹ * ((y + ε) ^ l)⁻¹ ≤ (Y.card : ℝ)
          · have hRkl : (ramsey k l : ℝ) ≤ (Y.card : ℝ) := by
              have hNle : N_R ≤ k + l := by
                have : N_R ≤ L₀ := by dsimp [L₀]; omega
                omega
              exact (hN_R k l hk (by omega) hNle).trans hYbig
            have hRnat : ramsey k l ≤ Y.card := by exact_mod_cast hRkl
            rcases hasRamsey_subset (ramsey_spec k l) G Y hRnat with ⟨s, hsY, hscl⟩ | ⟨s, hsY, hscl⟩
            · exact Or.inl ⟨s, hsY.trans Finset.subset_union_right, hscl⟩
            · exact Or.inr (Or.inr ⟨s, hsY, hscl⟩)
          · have hYlt : (Y.card : ℝ) < ((x + ε) ^ k)⁻¹ * ((y + ε) ^ l)⁻¹ := lt_of_not_ge hYbig
            -- Show (d(X, Y) + δkt - p)^r ≤ 1
            have hd_le_1 : dens G X Y + δkt - p ≤ 1 := by
              have h1 := dens_le_one G X Y
              linarith
            have hmom_le_XY : (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤ (X.card : ℝ) * (Y.card : ℝ) := by
              have hrle : (dens G X Y + δkt - p) ^ r ≤ 1 :=
                Real.rpow_le_one hgap_pos.le hd_le_1 hr0.le
              calc (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹
                  ≤ (dens G X Y + δkt - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) := hmom
                _ ≤ 1 * ((X.card : ℝ) * (Y.card : ℝ)) :=
                    mul_le_mul_of_nonneg_right hrle (by positivity)
                _ = (X.card : ℝ) * (Y.card : ℝ) := one_mul _
            -- Hence |X| ≥ ((x+ε)/x)^k * ((y+ε)/y)^l * μ^{-t} ≥ (1 + ε)^(k + l + t)
            have hX_lb : (1 + ε) ^ (k + l + t) ≤ (X.card : ℝ) := by
              have h1 : (1 + ε) ^ k ≤ (x + ε) ^ k * (x ^ k)⁻¹ := by
                have hpow : ((1 + ε) * x) ^ k ≤ (x + ε) ^ k :=
                  pow_le_pow_left₀ (by positivity) hx_ratio2 k
                rw [mul_pow] at hpow
                calc (1 + ε) ^ k = (1 + ε) ^ k * x ^ k * (x ^ k)⁻¹ := by
                      rw [mul_assoc, mul_inv_cancel₀ (pow_pos hx_pos k).ne', mul_one]
                  _ ≤ (x + ε) ^ k * (x ^ k)⁻¹ :=
                      mul_le_mul_of_nonneg_right hpow (by positivity)
              have h2 : (1 + ε) ^ l ≤ (y + ε) ^ l * (y ^ l)⁻¹ := by
                have hpow : ((1 + ε) * y) ^ l ≤ (y + ε) ^ l :=
                  pow_le_pow_left₀ (by positivity) hy_ratio2 l
                rw [mul_pow] at hpow
                calc (1 + ε) ^ l = (1 + ε) ^ l * y ^ l * (y ^ l)⁻¹ := by
                      rw [mul_assoc, mul_inv_cancel₀ (pow_pos hy_pos l).ne', mul_one]
                  _ ≤ (y + ε) ^ l * (y ^ l)⁻¹ :=
                      mul_le_mul_of_nonneg_right hpow (by positivity)
              have h3 : (1 + ε) ^ t ≤ (μ ^ t)⁻¹ := by
                have hμ1ε : (1 + ε) * μ ≤ 1 := by dsimp [μ]; nlinarith only [hε_pos, hε_μ1, hμ0]
                have hpow : ((1 + ε) * μ) ^ t ≤ 1 := pow_le_one₀ (by positivity) hμ1ε
                rw [mul_pow] at hpow
                have hmul := mul_le_mul_of_nonneg_right hpow (inv_nonneg.2 (pow_pos hμ_pos t).le)
                rw [mul_assoc, mul_inv_cancel₀ (pow_pos hμ_pos t).ne', mul_one, one_mul] at hmul
                exact hmul
              have hprod : (1 + ε) ^ (k + l + t) ≤
                  ((x + ε) ^ k * (x ^ k)⁻¹) * ((y + ε) ^ l * (y ^ l)⁻¹) * (μ ^ t)⁻¹ := by
                rw [pow_add, pow_add]
                exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
              have hYprod : (Y.card : ℝ) * ((x + ε) ^ k * (y + ε) ^ l) ≤ 1 := by
                have := mul_le_mul_of_nonneg_right hYlt.le (show 0 ≤ (x + ε) ^ k * (y + ε) ^ l by positivity)
                have hcancel : ((x + ε) ^ k)⁻¹ * ((y + ε) ^ l)⁻¹ * ((x + ε) ^ k * (y + ε) ^ l) = 1 := by
                  have h1 : (x + ε) ^ k ≠ 0 := (pow_pos (by linarith) k).ne'
                  have h2 : (y + ε) ^ l ≠ 0 := (pow_pos (by linarith) l).ne'
                  field_simp
                linarith
              calc (1 + ε) ^ (k + l + t)
                  ≤ ((x + ε) ^ k * (y + ε) ^ l) * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) := by
                    linarith [hprod]
                _ ≤ ((x + ε) ^ k * (y + ε) ^ l) * ((X.card : ℝ) * (Y.card : ℝ)) :=
                    mul_le_mul_of_nonneg_left hmom_le_XY (by positivity)
                _ = (X.card : ℝ) * ((Y.card : ℝ) * ((x + ε) ^ k * (y + ε) ^ l)) := by ring
                _ ≤ (X.card : ℝ) * 1 := mul_le_mul_of_nonneg_left hYprod hXpos.le
                _ = (X.card : ℝ) := mul_one _
            -- Step C (big blue step): define b, m, w
            let n : ℕ := k + l + t
            have hn_ge_L₀ : L₀ ≤ n := hl.trans (by omega : l ≤ n)
            have hn_ge_4 : 4 ≤ n := (le_max_right _ _).trans hn_ge_L₀
            have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
            have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
              have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_4
              have he : Real.exp 1 ≤ (n : ℝ) := by linarith [Real.exp_one_lt_d9]
              calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
                _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) he
            let b_real : ℝ := (2 * r * Real.log ((k : ℝ) + t) - r * Real.log ε + Real.log 2) / Real.log (1 + ε)
            let b : ℕ := max 1 ⌈b_real⌉₊
            have hb1 : 1 ≤ b := le_max_left _ _
            have hb_ge_real : b_real ≤ (b : ℝ) :=
              (Nat.le_ceil b_real).trans (by exact_mod_cast le_max_right 1 ⌈b_real⌉₊)
            have hb_ub : (b : ℝ) ≤ C_b * Real.log (n : ℝ) := by
              have hlogkt : Real.log ((k : ℝ) + t) ≤ Real.log (n : ℝ) :=
                Real.log_le_log hkt_pos (by exact_mod_cast (show k + t ≤ n by omega))
              have hbr_le : b_real ≤ (2 * r + |(-r * Real.log ε + Real.log 2)|) / Real.log (1 + ε) * Real.log (n : ℝ) := by
                dsimp [b_real]
                rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog1ε]
                have h1 : -r * Real.log ε + Real.log 2 ≤ |(-r * Real.log ε + Real.log 2)| := le_abs_self _
                have h2 : |(-r * Real.log ε + Real.log 2)| ≤ |(-r * Real.log ε + Real.log 2)| * Real.log (n : ℝ) :=
                  le_mul_of_one_le_right (abs_nonneg _) hlogn_ge1
                nlinarith only [hlogkt, h1, h2, hr0]
              have h1_le : (1 : ℝ) ≤ (2 / Real.log (1 + ε)) * Real.log (n : ℝ) := by
                have h1 : Real.log (1 + ε) ≤ ε := by
                  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + ε by linarith only [hε_pos])
                  linarith only [h]
                have h2 : Real.log (1 + ε) ≤ 2 := by linarith only [h1, hε_μ1, hμ0]
                rw [div_mul_eq_mul_div, one_le_div hlog1ε]
                nlinarith only [h2, hlogn_ge1]
              have hcb_split : C_b * Real.log (n : ℝ) =
                  (2 * r + |(-r * Real.log ε + Real.log 2)|) / Real.log (1 + ε) * Real.log (n : ℝ) +
                  (2 / Real.log (1 + ε)) * Real.log (n : ℝ) := by dsimp [C_b]; ring
              by_cases hceil : 1 ≤ ⌈b_real⌉₊
              · have hb_eq : b = ⌈b_real⌉₊ := max_eq_right hceil
                rw [hb_eq]
                by_cases hbr0 : 0 ≤ b_real
                · have hlt := Nat.ceil_lt_add_one hbr0
                  linarith
                · have hce0 : ⌈b_real⌉₊ = 0 := Nat.ceil_eq_zero.2 (le_of_not_ge hbr0)
                  omega
              · have hb_eq : b = 1 := max_eq_left (by omega)
                rw [hb_eq, Nat.cast_one]
                have hnn : 0 ≤ (2 * r + |(-r * Real.log ε + Real.log 2)|) / Real.log (1 + ε) * Real.log (n : ℝ) := by
                  have := abs_nonneg (-r * Real.log ε + Real.log 2); positivity
                linarith
            let m : ℕ := max 1 ⌈10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2⌉₊
            have hm1 : 1 ≤ m := le_max_left _ _
            have hm_ge : 10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2 ≤ (m : ℝ) :=
              (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right 1 _))
            have hm_ub : (m : ℝ) ≤ C_m * (Real.log (n : ℝ)) ^ 2 := by
              have hinv_le : (μ + ε)⁻¹ ≤ μ⁻¹ := inv_anti₀ hμ_pos (by linarith)
              have hterm : 10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2 ≤ 10 * μ⁻¹ * C_b ^ 2 * (Real.log (n : ℝ)) ^ 2 := by
                have hb2 : (b : ℝ) ^ 2 ≤ C_b ^ 2 * (Real.log (n : ℝ)) ^ 2 := by
                  rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg b) hb_ub 2
                have h1 : 10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2 ≤ 10 * μ⁻¹ * (b : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le (by norm_num)) (sq_nonneg _)
                have h2 : 10 * μ⁻¹ * (b : ℝ) ^ 2 ≤ 10 * μ⁻¹ * (C_b ^ 2 * (Real.log (n : ℝ)) ^ 2) :=
                  mul_le_mul_of_nonneg_left hb2 (by positivity)
                linarith
              have hlog2_ge1 : 1 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith only [hlogn_ge1]
              have hcm_eq : C_m * (Real.log (n : ℝ)) ^ 2 =
                  10 * μ⁻¹ * C_b ^ 2 * (Real.log (n : ℝ)) ^ 2 + 2 * (Real.log (n : ℝ)) ^ 2 := by
                dsimp [C_m]; ring
              by_cases hceil : 1 ≤ ⌈10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2⌉₊
              · have hm_eq : m = ⌈10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2⌉₊ := max_eq_right hceil
                rw [hm_eq]
                have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 10 * (μ + ε)⁻¹ * (b : ℝ) ^ 2 by positivity)
                linarith
              · have hm_eq : m = 1 := max_eq_left (by omega)
                rw [hm_eq, Nat.cast_one]
                have hnn : 0 ≤ 10 * μ⁻¹ * C_b ^ 2 * (Real.log (n : ℝ)) ^ 2 := by positivity
                linarith
            -- Bound |X| ≥ 5 m^2 and w = ramsey k m ≤ ε(p-ε)/(k+t)^3 * |X|
            have hX_ge_5m2 : 5 * (m : ℝ) ^ 2 ≤ (X.card : ℝ) := by
              have h1 : 5 * (m : ℝ) ^ 2 ≤ 5 * C_m ^ 2 * (Real.log (n : ℝ)) ^ 4 := by
                have hm2 : (m : ℝ) ^ 2 ≤ (C_m * (Real.log (n : ℝ)) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (Nat.cast_nonneg m) hm_ub 2
                nlinarith only [hm2]
              have hlog4 : (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ A_big := by
                have hln : Real.log (n : ℝ) ≤ (n : ℝ) :=
                  (Real.log_le_sub_one_of_pos hn_pos).trans (by linarith)
                have h4 : (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ (4 : ℝ) := by
                  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
                  exact pow_le_pow_left₀ (by linarith only [hlogn_ge1]) hln 4
                have hA4 : (4 : ℝ) ≤ A_big := by dsimp [A_big]; linarith [le_max_right r 3]
                exact h4.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hA4)
              have hK5 : 5 * C_m ^ 2 ≤ K_const := by
                have hle : 5 * C_m ^ 2 ≤ max (max (ε⁻¹ ^ r) (ε⁻¹ ^ 2)) (max (5 * C_m ^ 2) (ε * (p - ε))⁻¹) :=
                  (le_max_left _ _).trans (le_max_right _ _)
                dsimp [K_const]; linarith only [hle]
              have hexp1 : 1 ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) :=
                Real.one_le_exp (by positivity)
              calc 5 * (m : ℝ) ^ 2
                  ≤ 5 * C_m ^ 2 * (Real.log (n : ℝ)) ^ 4 := h1
                _ ≤ K_const * ((n : ℝ) ^ A_big * Real.exp (B_big * (Real.log (n : ℝ)) ^ 3)) := by
                    have hmul1 : 5 * C_m ^ 2 * (Real.log (n : ℝ)) ^ 4 ≤ K_const * (n : ℝ) ^ A_big :=
                      mul_le_mul hK5 hlog4 (by positivity) hK_pos.le
                    have hmul2 : K_const * (n : ℝ) ^ A_big ≤
                        K_const * ((n : ℝ) ^ A_big * Real.exp (B_big * (Real.log (n : ℝ)) ^ 3)) := by
                      rw [← mul_assoc]
                      exact le_mul_of_one_le_right (by positivity) hexp1
                    exact hmul1.trans hmul2
                _ ≤ (1 + ε) ^ n := hL₀_pow n hn_ge_L₀
                _ ≤ (X.card : ℝ) := hX_lb
            let w : ℕ := ramsey k m
            have hw_ub : (w : ℝ) ≤ ε * (p - ε) / ((k : ℝ) + t) ^ 3 * (X.card : ℝ) := by
              have hw_pow : (w : ℝ) ≤ ((k : ℝ) + m) ^ m := by
                exact_mod_cast ramsey_le_pow_add hk hm1
              have hm_le_n : (m : ℝ) ≤ (n : ℝ) := by
                have hn4 : N₄ ≤ n := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hn_ge_L₀
                exact hm_ub.trans (hN₄ n hn4)
              have hkm_le_n2 : (k : ℝ) + m ≤ (n : ℝ) ^ 2 := by
                have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n by omega)
                have hn2 : (2 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
                  have h4n : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_4
                  nlinarith only [h4n]
                linarith only [hk_le_n, hm_le_n, hn2]
              have hw_exp : (w : ℝ) ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) := by
                have hkm_pos : (0 : ℝ) < (k : ℝ) + m := by positivity
                calc (w : ℝ)
                    ≤ ((k : ℝ) + m) ^ m := hw_pow
                  _ ≤ ((n : ℝ) ^ 2) ^ m := pow_le_pow_left₀ hkm_pos.le hkm_le_n2 m
                  _ = Real.exp ((m : ℝ) * (2 * Real.log (n : ℝ))) := by
                      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (pow_pos hn_pos 2),
                          Real.log_pow]; ring_nf
                  _ ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) := by
                      apply Real.exp_le_exp.2
                      have h1 : (m : ℝ) * (2 * Real.log (n : ℝ)) ≤
                          (C_m * (Real.log (n : ℝ)) ^ 2) * (2 * Real.log (n : ℝ)) :=
                        mul_le_mul_of_nonneg_right hm_ub (by positivity)
                      have h2 : (C_m * (Real.log (n : ℝ)) ^ 2) * (2 * Real.log (n : ℝ)) =
                          (2 * C_m) * (Real.log (n : ℝ)) ^ 3 := by ring
                      have hB : 2 * C_m ≤ B_big := by dsimp [B_big]; linarith only []
                      have hlog3 : 0 ≤ (Real.log (n : ℝ)) ^ 3 := pow_nonneg (by linarith only [hlogn_ge1]) 3
                      nlinarith only [h1, h2, hB, hlog3]
              have hkt3 : ((k : ℝ) + t) ^ 3 ≤ (n : ℝ) ^ A_big := by
                have h1 : ((k : ℝ) + t) ^ 3 ≤ (n : ℝ) ^ 3 :=
                  pow_le_pow_left₀ hkt_pos.le (by exact_mod_cast (show k + t ≤ n by omega)) 3
                have h3 : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
                have hA3 : (3 : ℝ) ≤ A_big := by dsimp [A_big]; linarith [le_max_right r 3]
                exact h1.trans (h3.trans_le (Real.rpow_le_rpow_of_exponent_le
                  (by exact_mod_cast (show 1 ≤ n by omega)) hA3))
              have hKinv : (ε * (p - ε))⁻¹ ≤ K_const := by
                have hle : (ε * (p - ε))⁻¹ ≤ max (max (ε⁻¹ ^ r) (ε⁻¹ ^ 2)) (max (5 * C_m ^ 2) (ε * (p - ε))⁻¹) :=
                  (le_max_right _ _).trans (le_max_right _ _)
                dsimp [K_const]; linarith only [hle]
              have hpε : 0 < ε * (p - ε) := mul_pos hε_pos (by linarith)
              rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hkt_pos 3)]
              calc (w : ℝ) * ((k : ℝ) + t) ^ 3
                  ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) * (n : ℝ) ^ A_big :=
                    mul_le_mul hw_exp hkt3 (by positivity) (Real.exp_nonneg _)
                _ = ε * (p - ε) * ((ε * (p - ε))⁻¹ * ((n : ℝ) ^ A_big *
                      Real.exp (B_big * (Real.log (n : ℝ)) ^ 3))) := by
                    rw [← mul_assoc, mul_inv_cancel₀ hpε.ne', one_mul, mul_comm]
                _ ≤ ε * (p - ε) * (K_const * ((n : ℝ) ^ A_big *
                      Real.exp (B_big * (Real.log (n : ℝ)) ^ 3))) := by
                    apply mul_le_mul_of_nonneg_left _ hpε.le
                    exact mul_le_mul_of_nonneg_right hKinv (by positivity)
                _ ≤ ε * (p - ε) * (1 + ε) ^ n :=
                    mul_le_mul_of_nonneg_left (hL₀_pow n hn_ge_L₀) hpε.le
                _ ≤ ε * (p - ε) * (X.card : ℝ) :=
                    mul_le_mul_of_nonneg_left hX_lb hpε.le
            -- Define W = {v ∈ X | |N_B(v) ∩ X| ≥ (μ + ε) |X|}
            set W : Finset V := X.filter (fun v => (μ + ε) * (X.card : ℝ) ≤
              ((X.filter (fun u => v ≠ u ∧ ¬ G.Adj v u)).card : ℝ))
            by_cases hWbig : w ≤ W.card
            · -- Apply Blue Book Lemma
              rcases blue_book_lemma G (by linarith : 0 < μ + ε) hμ_add_lt1 hb1 hk hm1 hm_ge
                  X hX_ge_5m2 hWbig with ⟨s, hsX, hscl⟩ | ⟨S, T, hSX, hTX, hSTdisj, hScl, hSTblue, hTcard⟩
              · exact Or.inl ⟨s, hsX.trans Finset.subset_union_left, hscl⟩
              · by_cases hbt : t ≤ b
                · obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq (hScl.card_eq ▸ hbt)
                  exact Or.inr (Or.inl ⟨S', hS'S.trans hSX, hScl.1.subset hS'S, hS'c⟩)
                · have htb_pos : 1 ≤ t - b := by omega
                  have hTne : T.Nonempty := by
                    have hTpos : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le (by positivity) hTcard
                    exact Finset.card_pos.1 (by exact_mod_cast hTpos)
                  have hdTY : p - δkt ≤ dens G T Y := hdeg_sub T hTX hTne
                  have hδ_diff : ε / ((k : ℝ) + t) ^ 2 ≤ ε / ((k : ℝ) + (t - b : ℕ)) - δkt := by
                    have hlt_kt : (k : ℝ) + (t - b : ℕ) ≤ (k : ℝ) + t - 1 := by
                      have : k + (t - b) + 1 ≤ k + t := by omega
                      have : ((k + (t - b) + 1 : ℕ) : ℝ) ≤ ((k + t : ℕ) : ℝ) := by exact_mod_cast this
                      push_cast at this; linarith
                    have hden_pos : (0 : ℝ) < (k : ℝ) + (t - b : ℕ) := by positivity
                    have h1 : ε / ((k : ℝ) + t - 1) ≤ ε / ((k : ℝ) + (t - b : ℕ)) :=
                      div_le_div_of_nonneg_left hε_pos.le hden_pos hlt_kt
                    have h2 : ε / ((k : ℝ) + t) ^ 2 ≤ ε / ((k : ℝ) + t - 1) - ε / ((k : ℝ) + t) := by
                      have hkt1 : (0 : ℝ) < (k : ℝ) + t - 1 := by
                        have : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                        linarith
                      rw [div_sub_div _ _ hkt1.ne' hkt_pos.ne']
                      rw [div_le_div_iff₀ (pow_pos hkt_pos 2) (mul_pos hkt1 hkt_pos)]
                      nlinarith only [hε_pos, hkt_pos]
                    dsimp [δkt]; linarith only [h1, h2]
                  have hdTY2 : p - ε / ((k : ℝ) + (t - b : ℕ)) ≤ dens G T Y := by
                    have hnn : (0 : ℝ) ≤ ε / ((k : ℝ) + t) ^ 2 := by positivity
                    linarith only [hdTY, hδ_diff, hnn]
                  have hgapTY : ε / ((k : ℝ) + t) ^ 2 ≤ dens G T Y + ε / ((k : ℝ) + (t - b : ℕ)) - p := by
                    linarith only [hdTY, hδ_diff]
                  -- Check ((μ + ε) / μ)^b ≥ 2 * ((k + t)^2 / ε)^r
                  have hμ_pow_b : 2 * (((k : ℝ) + t) ^ 2 / ε) ^ r ≤ ((μ + ε) / μ) ^ b := by
                    have hrat : 1 + ε ≤ (μ + ε) / μ := by
                      rw [le_div_iff₀ hμ_pos]; nlinarith only [hε_pos, hμ_lt1]
                    have hlog_goal : Real.log (2 * (((k : ℝ) + t) ^ 2 / ε) ^ r) ≤
                        (b : ℝ) * Real.log (1 + ε) := by
                      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (by positivity) _).ne',
                          Real.log_rpow (by positivity),
                          Real.log_div (pow_pos hkt_pos 2).ne' hε_pos.ne',
                          Real.log_pow]
                      have hbr := (div_le_iff₀ hlog1ε).1 hb_ge_real
                      push_cast; linarith
                    have hexp_b : 2 * (((k : ℝ) + t) ^ 2 / ε) ^ r ≤ (1 + ε) ^ b := by
                      have h1 := Real.exp_le_exp.2 hlog_goal
                      rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by linarith)] at h1
                      exact h1
                    exact hexp_b.trans (pow_le_pow_left₀ (by linarith) hrat b)
                  have hmomT : (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - b))⁻¹ ≤
                      (dens G T Y + ε / ((k : ℝ) + (t - b : ℕ)) - p) ^ r * ((T.card : ℝ) * (Y.card : ℝ)) := by
                    have h1 : (ε / ((k : ℝ) + t) ^ 2) ^ r ≤
                        (dens G T Y + ε / ((k : ℝ) + (t - b : ℕ)) - p) ^ r :=
                      Real.rpow_le_rpow (by positivity) hgapTY hr0.le
                    have hinv_r : (ε / ((k : ℝ) + t) ^ 2) ^ r * (((k : ℝ) + t) ^ 2 / ε) ^ r = 1 := by
                      rw [← Real.mul_rpow (by positivity) (by positivity)]
                      have : ε / ((k : ℝ) + t) ^ 2 * (((k : ℝ) + t) ^ 2 / ε) = 1 := by
                        field_simp [hε_pos.ne', hkt_pos.ne']
                      rw [this, Real.one_rpow]
                    have hμ_split : (μ + ε) ^ b * (μ ^ t)⁻¹ = ((μ + ε) / μ) ^ b * (μ ^ (t - b))⁻¹ := by
                      have htb : t = b + (t - b) := by omega
                      conv_lhs => rw [htb]
                      rw [pow_add, mul_inv, div_pow]
                      have hμb : μ ^ b ≠ 0 := (pow_pos hμ_pos b).ne'
                      field_simp
                    calc (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - b))⁻¹
                        = ((ε / ((k : ℝ) + t) ^ 2) ^ r * (((k : ℝ) + t) ^ 2 / ε) ^ r) *
                            ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - b))⁻¹) := by rw [hinv_r, one_mul]
                      _ ≤ (ε / ((k : ℝ) + t) ^ 2) ^ r * (((μ + ε) / μ) ^ b / 2) *
                            ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - b))⁻¹) := by
                          have hle : (((k : ℝ) + t) ^ 2 / ε) ^ r ≤ ((μ + ε) / μ) ^ b / 2 := by linarith only [hμ_pow_b]
                          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
                      _ = (ε / ((k : ℝ) + t) ^ 2) ^ r * ((μ + ε) ^ b / 2) *
                            ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) := by
                          have : ((μ + ε) / μ) ^ b / 2 * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - b))⁻¹) =
                              ((μ + ε) ^ b / 2) * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) := by
                            calc _ = (x ^ k)⁻¹ * (y ^ l)⁻¹ * (((μ + ε) / μ) ^ b * (μ ^ (t - b))⁻¹) / 2 := by ring
                              _ = (x ^ k)⁻¹ * (y ^ l)⁻¹ * ((μ + ε) ^ b * (μ ^ t)⁻¹) / 2 := by rw [← hμ_split]
                              _ = _ := by ring
                          rw [mul_assoc, this, ← mul_assoc]
                      _ ≤ (ε / ((k : ℝ) + t) ^ 2) ^ r * ((μ + ε) ^ b / 2) * ((X.card : ℝ) * (Y.card : ℝ)) :=
                          mul_le_mul_of_nonneg_left hmom_le_XY (by positivity)
                      _ = (ε / ((k : ℝ) + t) ^ 2) ^ r * (((μ + ε) ^ b / 2 * (X.card : ℝ)) * (Y.card : ℝ)) := by ring
                      _ ≤ (dens G T Y + ε / ((k : ℝ) + (t - b : ℕ)) - p) ^ r * ((T.card : ℝ) * (Y.card : ℝ)) :=
                          mul_le_mul h1 (mul_le_mul_of_nonneg_right hTcard hYpos.le) (by positivity)
                            (Real.rpow_nonneg (by linarith only [hgapTY, show (0 : ℝ) ≤ ε / ((k : ℝ) + t) ^ 2 by positivity]) r)
                  have hTgood := ih (k + (t - b)) (by omega) k (t - b) rfl hk htb_pos T Y
                    hTne hYne (Disjoint.mono_left hTX hdisj) hdTY2 hmomT
                  rcases hTgood with ⟨s, hsTY, hscl⟩ | ⟨s, hsT, hscl⟩ | ⟨s, hsY, hscl⟩
                  · exact Or.inl ⟨s, hsTY.trans (Finset.union_subset_union_left hTX), hscl⟩
                  · right; left
                    refine ⟨S ∪ s, Finset.union_subset hSX (hsT.trans hTX), ?_, ?_⟩
                    · intro u hu v hv huv
                      rcases Finset.mem_union.1 hu with huS | hus <;>
                      rcases Finset.mem_union.1 hv with hvS | hvs
                      · exact hScl.1 huS hvS huv
                      · exact hSTblue u huS v (hsT hvs)
                      · exact (Gᶜ.adj_comm _ _).1 (hSTblue v hvS u (hsT hus))
                      · exact hscl.1 hus hvs huv
                    · have hdisjSs : Disjoint S s := Disjoint.mono_right hsT hSTdisj
                      rw [Finset.card_union_of_disjoint hdisjSs, hScl.card_eq, hscl.card_eq]
                      omega
                  · exact Or.inr (Or.inr ⟨s, hsY, hscl⟩)
            · -- Step D: |W| < w; find v ∈ X \ W via convexity of density
              have hWle : (W.card : ℝ) ≤ (w : ℝ) := by exact_mod_cast (show W.card ≤ w by omega)
              have hconv := sum_dens_redNbhd_ge G hXne hYne
              have hWsum : ∑ v ∈ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) ≤
                  (ε / ((k : ℝ) + t) ^ 3) * (redEdges G X Y : ℝ) := by
                have h1 : ∑ v ∈ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) ≤
                    (W.card : ℝ) * (Y.card : ℝ) := by
                  calc _ ≤ ∑ _v ∈ W, (1 : ℝ) * (Y.card : ℝ) :=
                        Finset.sum_le_sum fun v _ => mul_le_mul (dens_le_one G X _)
                          (by exact_mod_cast Finset.card_filter_le Y (G.Adj v)) (Nat.cast_nonneg _) zero_le_one
                    _ = (W.card : ℝ) * (Y.card : ℝ) := by simp
                have heR_lb : (p - ε) * ((X.card : ℝ) * (Y.card : ℝ)) ≤ (redEdges G X Y : ℝ) := by
                  have hd : p - ε ≤ dens G X Y := by linarith
                  unfold dens at hd
                  exact (le_div_iff₀ (mul_pos hXpos hYpos)).1 hd
                calc _ ≤ (W.card : ℝ) * (Y.card : ℝ) := h1
                  _ ≤ (w : ℝ) * (Y.card : ℝ) := mul_le_mul_of_nonneg_right hWle hYpos.le
                  _ ≤ (ε * (p - ε) / ((k : ℝ) + t) ^ 3 * (X.card : ℝ)) * (Y.card : ℝ) :=
                      mul_le_mul_of_nonneg_right hw_ub hYpos.le
                  _ = (ε / ((k : ℝ) + t) ^ 3) * ((p - ε) * ((X.card : ℝ) * (Y.card : ℝ))) := by ring
                  _ ≤ (ε / ((k : ℝ) + t) ^ 3) * (redEdges G X Y : ℝ) :=
                      mul_le_mul_of_nonneg_left heR_lb (by positivity)
              have hsplit : ∑ v ∈ X \ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) +
                  ∑ v ∈ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) =
                  ∑ v ∈ X, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) :=
                Finset.sum_sdiff (Finset.filter_subset _ X)
              have hXW_sum : (dens G X Y - ε / ((k : ℝ) + t) ^ 3) * (redEdges G X Y : ℝ) ≤
                  ∑ v ∈ X \ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) := by
                linarith
              have hdens_sub_pos : 0 < dens G X Y - ε / ((k : ℝ) + t) ^ 3 := by
                have h1 : ε / ((k : ℝ) + t) ^ 3 ≤ ε := by
                  rw [div_le_iff₀ (pow_pos hkt_pos 3)]
                  have h4kt : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                  have h1kt : (1 : ℝ) ≤ ((k : ℝ) + t) ^ 3 := one_le_pow₀ (by linarith only [h4kt])
                  nlinarith only [h1kt, hε_pos]
                linarith only [h1, hdens_step, hδkt_le_ε, hε_p, hε_pos]
              have heR_pos : (0 : ℝ) < (redEdges G X Y : ℝ) := by
                have hd : p - ε ≤ dens G X Y := by linarith only [hdens_step, hδkt_le_ε]
                unfold dens at hd
                have h1 := (le_div_iff₀ (mul_pos hXpos hYpos)).1 hd
                have hpos : 0 < (p - ε) * ((X.card : ℝ) * (Y.card : ℝ)) :=
                  mul_pos (by linarith only [hε_p, hε_pos]) (mul_pos hXpos hYpos)
                linarith only [h1, hpos]
              -- Pick v ∈ X \ W with d(X, N_R(v) ∩ Y) ≥ d(X, Y) - ε / (k + t)^3
              have hex_v : ∃ v ∈ X \ W,
                  dens G X Y - ε / ((k : ℝ) + t) ^ 3 ≤ dens G X (Y.filter (G.Adj v)) := by
                by_contra hall
                push Not at hall
                have hsum_deg_le : ∑ v ∈ X \ W, ((Y.filter (G.Adj v)).card : ℝ) ≤ (redEdges G X Y : ℝ) := by
                  rw [redEdges_eq_sum_card_filter]
                  have : ∑ v ∈ X \ W, (Y.filter (G.Adj v)).card ≤ ∑ v ∈ X, (Y.filter (G.Adj v)).card :=
                    Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
                  exact_mod_cast this
                have hsum_lt : ∑ v ∈ X \ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) <
                    (dens G X Y - ε / ((k : ℝ) + t) ^ 3) * (redEdges G X Y : ℝ) := by
                  by_cases hzero : ∑ v ∈ X \ W, ((Y.filter (G.Adj v)).card : ℝ) = 0
                  · have hall0 : ∀ v ∈ X \ W, ((Y.filter (G.Adj v)).card : ℝ) = 0 :=
                      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 hzero
                    have hls0 : ∑ v ∈ X \ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) = 0 :=
                      Finset.sum_eq_zero fun v hv => by rw [hall0 v hv, mul_zero]
                    rw [hls0]
                    exact mul_pos hdens_sub_pos heR_pos
                  · have hpos_s : 0 < ∑ v ∈ X \ W, ((Y.filter (G.Adj v)).card : ℝ) :=
                      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Ne.symm hzero)
                    have hex_pos : ∃ v ∈ X \ W, (0 : ℝ) < ((Y.filter (G.Adj v)).card : ℝ) := by
                      by_contra hnp; push Not at hnp
                      have := Finset.sum_eq_zero fun v hv =>
                        le_antisymm (hnp v hv) (Nat.cast_nonneg _)
                      exact hzero this
                    have hstrict : ∑ v ∈ X \ W, dens G X (Y.filter (G.Adj v)) * ((Y.filter (G.Adj v)).card : ℝ) <
                        ∑ v ∈ X \ W, (dens G X Y - ε / ((k : ℝ) + t) ^ 3) * ((Y.filter (G.Adj v)).card : ℝ) := by
                      apply Finset.sum_lt_sum
                      · intro v hv
                        exact mul_le_mul_of_nonneg_right (hall v hv).le (Nat.cast_nonneg _)
                      · obtain ⟨v₀, hv₀, hv₀pos⟩ := hex_pos
                        exact ⟨v₀, hv₀, mul_lt_mul_of_pos_right (hall v₀ hv₀) hv₀pos⟩
                    rw [← Finset.mul_sum] at hstrict
                    exact hstrict.trans_le (mul_le_mul_of_nonneg_left hsum_deg_le hdens_sub_pos.le)
                linarith
              obtain ⟨v, hvXW, hv_dens⟩ := hex_v
              have hvX : v ∈ X := (Finset.mem_sdiff.1 hvXW).1
              have hvNotW : v ∉ W := (Finset.mem_sdiff.1 hvXW).2
              -- Set p' = p - δ_{k+t-1}, X_R, X_B, Y'
              set p' : ℝ := p - ε / ((k : ℝ) + t - 1)
              set XR : Finset V := X.filter (G.Adj v)
              set XB : Finset V := X.filter (fun u => v ≠ u ∧ ¬ G.Adj v u)
              set Y' : Finset V := Y.filter (G.Adj v)
              have hXB_le : (XB.card : ℝ) < (μ + ε) * (X.card : ℝ) := by
                by_contra hge
                exact hvNotW (Finset.mem_filter.2 ⟨hvX, le_of_not_gt hge⟩)
              have hY'_lb : (p - ε) * (Y.card : ℝ) ≤ (Y'.card : ℝ) := by
                have h1 := hdeg_all v hvX
                have h2 : p - ε ≤ p - δkt := by linarith
                exact (mul_le_mul_of_nonneg_right h2 hYpos.le).trans h1
              have hY'pos : (0 : ℝ) < Y'.card := lt_of_lt_of_le (mul_pos (by linarith) hYpos) hY'_lb
              have hY'ne : Y'.Nonempty := Finset.card_pos.1 (by exact_mod_cast hY'pos)
              set α : ℝ := dens G X Y' - p'
              set αR : ℝ := dens G XR Y' - p'
              set αB : ℝ := dens G XB Y' - p'
              have hkt1_pos : (0 : ℝ) < (k : ℝ) + t - 1 := by
                have : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                linarith
              have hα_ge_gap : dens G X Y + δkt - p ≤ α := by
                have hdiff : ε / ((k : ℝ) + t) ^ 3 ≤ ε / ((k : ℝ) + t - 1) - δkt := by
                  dsimp [δkt]
                  rw [div_sub_div _ _ hkt1_pos.ne' hkt_pos.ne',
                      div_le_div_iff₀ (pow_pos hkt_pos 3) (mul_pos hkt1_pos hkt_pos)]
                  have h4kt : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                  have hpoly : ((k : ℝ) + t - 1) * ((k : ℝ) + t) ≤ ((k : ℝ) + t) ^ 3 := by
                    have hc : ((k : ℝ) + t) ^ 3 = ((k : ℝ) + t) * ((k : ℝ) + t) ^ 2 := by ring
                    nlinarith only [h4kt, hc]
                  nlinarith only [hpoly, hε_pos]
                dsimp [α, p']
                linarith only [hv_dens, hdiff]
              have hα_lb : ε / ((k : ℝ) + t) ^ 2 ≤ α := by
                have hdiff : ε / ((k : ℝ) + t) ^ 2 + ε / ((k : ℝ) + t) ^ 3 ≤
                    ε / ((k : ℝ) + t - 1) - δkt := by
                  dsimp [δkt]
                  rw [div_sub_div _ _ hkt1_pos.ne' hkt_pos.ne']
                  have heq : ε / ((k : ℝ) + t) ^ 2 + ε / ((k : ℝ) + t) ^ 3 =
                      ε * ((k : ℝ) + t + 1) / ((k : ℝ) + t) ^ 3 := by
                    field_simp [hkt_pos.ne']
                  rw [heq, div_le_div_iff₀ (pow_pos hkt_pos 3) (mul_pos hkt1_pos hkt_pos)]
                  have h4kt : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                  have hdiff_id : (ε * ((k : ℝ) + t) - ε * ((k : ℝ) + t - 1)) * ((k : ℝ) + t) ^ 3 -
                      ε * ((k : ℝ) + t + 1) * (((k : ℝ) + t - 1) * ((k : ℝ) + t)) =
                      ε * ((k : ℝ) + t) := by ring
                  nlinarith only [hdiff_id, h4kt, hε_pos]
                dsimp [α, p']
                linarith only [hv_dens, hdens_step, hdiff]
              have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα_lb
              -- Partition X = XR ∪ XB ∪ {v}
              have hdisj_RB : Disjoint XR XB := by
                rw [Finset.disjoint_left]
                intro u huR huB
                exact (Finset.mem_filter.1 huB).2.2 (Finset.mem_filter.1 huR).2
              have hv_not_R : v ∉ XR := fun hvR => G.ne_of_adj (Finset.mem_filter.1 hvR).2 rfl
              have hv_not_B : v ∉ XB := fun hvB => (Finset.mem_filter.1 hvB).2.1 rfl
              have hX_part : X = insert v (XR ∪ XB) := by
                ext u
                simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, XR, XB]
                constructor
                · intro huX
                  by_cases huv : u = v
                  · exact Or.inl huv
                  · right
                    by_cases hadj : G.Adj v u
                    · exact Or.inl ⟨huX, hadj⟩
                    · exact Or.inr ⟨huX, Ne.symm huv, hadj⟩
                · rintro (rfl | ⟨huX, _⟩ | ⟨huX, _⟩)
                  · exact hvX
                  · exact huX
                  · exact huX
              have hcard_part : XR.card + XB.card + 1 = X.card := by
                have h1 : (insert v (XR ∪ XB)).card = (XR ∪ XB).card + 1 :=
                  Finset.card_insert_of_notMem (by simp [hv_not_R, hv_not_B])
                rw [hX_part, h1, Finset.card_union_of_disjoint hdisj_RB]
              have heR_part : redEdges G X Y' = redEdges G XR Y' + redEdges G XB Y' + Y'.card := by
                have hv_not_union : v ∉ XR ∪ XB := by simp [hv_not_R, hv_not_B]
                have he1 : redEdges G X Y' = redEdges G (XR ∪ XB) Y' + (Y'.filter (G.Adj v)).card := by
                  rw [hX_part]
                  have := redEdges_erase_left G (X := insert v (XR ∪ XB)) (Y := Y') (v := v)
                    (Finset.mem_insert_self v _)
                  rw [Finset.erase_insert hv_not_union] at this
                  exact this.symm
                have hY'f : Y'.filter (G.Adj v) = Y' := by
                  ext u; simp [Y']
                rw [he1, redEdges_disj_union_left G hdisj_RB, hY'f]
              clear hX_part
              -- Equation (e:moment2): αR/α * |XR|/|X| + αB/α * |XB|/|X| + 1/(α|X|) ≥ 1
              have hmoment2 : αR / α * ((XR.card : ℝ) / (X.card : ℝ)) +
                  αB / α * ((XB.card : ℝ) / (X.card : ℝ)) + 1 / (α * (X.card : ℝ)) ≥ 1 := by
                have h1 : (αR * (XR.card : ℝ) + αB * (XB.card : ℝ) + 1) * (Y'.card : ℝ) ≥
                    α * (X.card : ℝ) * (Y'.card : ℝ) := by
                  have hXR_e : dens G XR Y' * (XR.card : ℝ) * (Y'.card : ℝ) = (redEdges G XR Y' : ℝ) := by
                    by_cases hne : XR.Nonempty
                    · exact dens_mul_cards G hne hY'ne
                    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp [redEdges]
                  have hXB_e : dens G XB Y' * (XB.card : ℝ) * (Y'.card : ℝ) = (redEdges G XB Y' : ℝ) := by
                    by_cases hne : XB.Nonempty
                    · exact dens_mul_cards G hne hY'ne
                    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp [redEdges]
                  have hX_e : dens G X Y' * (X.card : ℝ) * (Y'.card : ℝ) = (redEdges G X Y' : ℝ) :=
                    dens_mul_cards G hXne hY'ne
                  have heR_r : (redEdges G X Y' : ℝ) = (redEdges G XR Y' : ℝ) + (redEdges G XB Y' : ℝ) + (Y'.card : ℝ) := by
                    exact_mod_cast heR_part
                  have hcard_r : (XR.card : ℝ) + (XB.card : ℝ) + 1 = (X.card : ℝ) := by
                    exact_mod_cast hcard_part
                  have hεkt1 : ε / ((k : ℝ) + t - 1) ≤ ε := by
                    rw [div_le_iff₀ hkt1_pos]
                    have h4kt : (4 : ℝ) ≤ (k : ℝ) + t := by exact_mod_cast (show 4 ≤ k + t by omega)
                    nlinarith only [h4kt, hε_pos]
                  have hp'nn : 0 ≤ p' := by dsimp [p']; linarith only [hεkt1, hε_p, hε_pos]
                  have hdiff_e : ((dens G XR Y' - p') * (XR.card : ℝ) + (dens G XB Y' - p') * (XB.card : ℝ) + 1) * (Y'.card : ℝ) -
                      (dens G X Y' - p') * (X.card : ℝ) * (Y'.card : ℝ) = p' * (Y'.card : ℝ) := by
                    linear_combination hXR_e + hXB_e - hX_e - heR_r - p' * (Y'.card : ℝ) * hcard_r
                  dsimp [α, αR, αB]
                  nlinarith only [hdiff_e, hp'nn, hY'pos]
                have h2 : α * (X.card : ℝ) ≤ αR * (XR.card : ℝ) + αB * (XB.card : ℝ) + 1 :=
                  le_of_mul_le_mul_right h1 hY'pos
                have hdiv := div_le_div_of_nonneg_right h2 (mul_pos hα_pos hXpos).le
                rw [div_self (mul_pos hα_pos hXpos).ne'] at hdiv
                have heq : (αR * (XR.card : ℝ) + αB * (XB.card : ℝ) + 1) / (α * (X.card : ℝ)) =
                    αR / α * ((XR.card : ℝ) / (X.card : ℝ)) +
                    αB / α * ((XB.card : ℝ) / (X.card : ℝ)) + 1 / (α * (X.card : ℝ)) := by
                  field_simp [hα_pos.ne', hXpos.ne']
                linarith only [hdiv, heq]
              have hpε_pos : 0 < p - ε := by linarith only [hε_p, hε_pos]
              -- Check red branch: if αR ≥ 0 and αR^r * |XR| ≥ x * α^r * |X| / (p - ε), apply IH to (XR, Y')
              by_cases hRstep : 0 ≤ αR ∧ x * α ^ r * (X.card : ℝ) / (p - ε) ≤ αR ^ r * (XR.card : ℝ)
              · rcases hRstep with ⟨hαR_nn, hαR_ge⟩
                have hXRne : XR.Nonempty := by
                  by_contra hne
                  rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero, mul_zero] at hαR_ge
                  have hpos_l : 0 < x * α ^ r * (X.card : ℝ) / (p - ε) :=
                    div_pos (mul_pos (mul_pos hx_pos (Real.rpow_pos_of_pos hα_pos r)) hXpos) (by linarith)
                  linarith
                have hmomR : (x ^ (k - 1))⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤
                    (dens G XR Y' + ε / ((k - 1 : ℕ) + (t : ℝ)) - p) ^ r * ((XR.card : ℝ) * (Y'.card : ℝ)) := by
                  have hkt_eq : ((k - 1 : ℕ) : ℝ) + (t : ℝ) = (k : ℝ) + t - 1 := by
                    rw [Nat.cast_sub hk, Nat.cast_one]; ring
                  rw [hkt_eq]
                  have hd_eq : dens G XR Y' + ε / ((k : ℝ) + t - 1) - p = αR := by dsimp [αR, p']; ring
                  rw [hd_eq]
                  have hxk : (x ^ (k - 1))⁻¹ = x * (x ^ k)⁻¹ := by
                    have h1 : k = (k - 1) + 1 := by omega
                    conv_rhs => rw [h1, pow_succ, mul_inv]
                    field_simp [hx_pos.ne']
                  have hα_r : (dens G X Y + δkt - p) ^ r ≤ α ^ r :=
                    Real.rpow_le_rpow hgap_pos.le hα_ge_gap hr0.le
                  calc (x ^ (k - 1))⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹
                      = x * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) := by rw [hxk]; ring
                    _ ≤ x * ((dens G X Y + δkt - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ))) :=
                        mul_le_mul_of_nonneg_left hmom hx_pos.le
                    _ ≤ x * (α ^ r * ((X.card : ℝ) * (Y.card : ℝ))) :=
                        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hα_r (by positivity)) hx_pos.le
                    _ = (x * α ^ r * (X.card : ℝ) / (p - ε)) * ((p - ε) * (Y.card : ℝ)) := by
                        field_simp [(show (0 : ℝ) < p - ε by linarith).ne']
                    _ ≤ (αR ^ r * (XR.card : ℝ)) * (Y'.card : ℝ) :=
                        mul_le_mul hαR_ge hY'_lb (by positivity) (by positivity)
                    _ = αR ^ r * ((XR.card : ℝ) * (Y'.card : ℝ)) := by ring
                have hdR : p - ε / ((k - 1 : ℕ) + (t : ℝ)) ≤ dens G XR Y' := by
                  have hkt_eq : ((k - 1 : ℕ) : ℝ) + (t : ℝ) = (k : ℝ) + t - 1 := by
                    rw [Nat.cast_sub hk, Nat.cast_one]; ring
                  rw [hkt_eq]; dsimp [αR, p'] at hαR_nn; linarith
                have hRgood := ih ((k - 1) + t) (by omega) (k - 1) t rfl (by omega) ht XR Y'
                  hXRne hY'ne (Disjoint.mono (Finset.filter_subset _ X) (Finset.filter_subset _ Y) hdisj)
                  hdR hmomR
                rcases hRgood with ⟨s, hsRY, hscl⟩ | ⟨s, hsR, hscl⟩ | ⟨s, hsY', hscl⟩
                · left
                  refine ⟨insert v s, ?_, ?_, ?_⟩
                  · exact Finset.insert_subset (Finset.mem_union_left _ hvX)
                      (hsRY.trans (Finset.union_subset_union (Finset.filter_subset _ X) (Finset.filter_subset _ Y)))
                  · intro u hu w hw huw
                    rcases Finset.mem_insert.1 hu with rfl | hus <;>
                    rcases Finset.mem_insert.1 hw with rfl | hws
                    · exact False.elim (huw rfl)
                    · rcases Finset.mem_union.1 (hsRY hws) with h1 | h2
                      · exact (Finset.mem_filter.1 h1).2
                      · exact (Finset.mem_filter.1 h2).2
                    · rcases Finset.mem_union.1 (hsRY hus) with h1 | h2
                      · exact (G.adj_comm _ _).1 (Finset.mem_filter.1 h1).2
                      · exact (G.adj_comm _ _).1 (Finset.mem_filter.1 h2).2
                    · exact hscl.1 hus hws huw
                  · have hv_not_s : v ∉ s := fun hvs => by
                      rcases Finset.mem_union.1 (hsRY hvs) with h1 | h2
                      · exact hv_not_R h1
                      · exact Finset.disjoint_left.1 hdisj hvX (Finset.filter_subset _ Y h2)
                    rw [Finset.card_insert_of_notMem hv_not_s, hscl.card_eq]; omega
                · exact Or.inr (Or.inl ⟨s, hsR.trans (Finset.filter_subset _ X), hscl⟩)
                · exact Or.inr (Or.inr ⟨s, hsY'.trans (Finset.filter_subset _ Y), hscl⟩)
              · -- Check blue branch: if αB ≥ 0 and αB^r * |XB| ≥ μ * α^r * |X| / (p - ε), apply IH to (XB, Y')
                by_cases hBstep : 0 ≤ αB ∧ μ * α ^ r * (X.card : ℝ) / (p - ε) ≤ αB ^ r * (XB.card : ℝ)
                · rcases hBstep with ⟨hαB_nn, hαB_ge⟩
                  have hXBne : XB.Nonempty := by
                    by_contra hne
                    rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero, mul_zero] at hαB_ge
                    have hpos_l : 0 < μ * α ^ r * (X.card : ℝ) / (p - ε) :=
                      div_pos (mul_pos (mul_pos hμ_pos (Real.rpow_pos_of_pos hα_pos r)) hXpos) (by linarith)
                    linarith
                  have hmomB : (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - 1))⁻¹ ≤
                      (dens G XB Y' + ε / ((k : ℝ) + (t - 1 : ℕ)) - p) ^ r * ((XB.card : ℝ) * (Y'.card : ℝ)) := by
                    have hkt_eq : (k : ℝ) + ((t - 1 : ℕ) : ℝ) = (k : ℝ) + t - 1 := by
                      rw [Nat.cast_sub ht, Nat.cast_one]; ring
                    rw [hkt_eq]
                    have hd_eq : dens G XB Y' + ε / ((k : ℝ) + t - 1) - p = αB := by dsimp [αB, p']; ring
                    rw [hd_eq]
                    have hμt : (μ ^ (t - 1))⁻¹ = μ * (μ ^ t)⁻¹ := by
                      have h1 : t = (t - 1) + 1 := by omega
                      conv_rhs => rw [h1, pow_succ, mul_inv]
                      field_simp [hμ_pos.ne']
                    have hα_r : (dens G X Y + δkt - p) ^ r ≤ α ^ r :=
                      Real.rpow_le_rpow hgap_pos.le hα_ge_gap hr0.le
                    calc (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ (t - 1))⁻¹
                        = μ * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) := by rw [hμt]; ring
                      _ ≤ μ * ((dens G X Y + δkt - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ))) :=
                          mul_le_mul_of_nonneg_left hmom hμ_pos.le
                      _ ≤ μ * (α ^ r * ((X.card : ℝ) * (Y.card : ℝ))) :=
                          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hα_r (by positivity)) hμ_pos.le
                      _ = (μ * α ^ r * (X.card : ℝ) / (p - ε)) * ((p - ε) * (Y.card : ℝ)) := by
                          field_simp [(show (0 : ℝ) < p - ε by linarith).ne']
                      _ ≤ (αB ^ r * (XB.card : ℝ)) * (Y'.card : ℝ) :=
                          mul_le_mul hαB_ge hY'_lb (by positivity) (by positivity)
                      _ = αB ^ r * ((XB.card : ℝ) * (Y'.card : ℝ)) := by ring
                  have hdB : p - ε / ((k : ℝ) + (t - 1 : ℕ)) ≤ dens G XB Y' := by
                    have hkt_eq : (k : ℝ) + ((t - 1 : ℕ) : ℝ) = (k : ℝ) + t - 1 := by
                      rw [Nat.cast_sub ht, Nat.cast_one]; ring
                    rw [hkt_eq]; dsimp [αB, p'] at hαB_nn; linarith
                  have hBgood := ih (k + (t - 1)) (by omega) k (t - 1) rfl hk (by omega) XB Y'
                    hXBne hY'ne (Disjoint.mono (Finset.filter_subset _ X) (Finset.filter_subset _ Y) hdisj)
                    hdB hmomB
                  rcases hBgood with ⟨s, hsBY, hscl⟩ | ⟨s, hsB, hscl⟩ | ⟨s, hsY', hscl⟩
                  · exact Or.inl ⟨s, hsBY.trans (Finset.union_subset_union (Finset.filter_subset _ X) (Finset.filter_subset _ Y)), hscl⟩
                  · right; left
                    refine ⟨insert v s, Finset.insert_subset hvX (hsB.trans (Finset.filter_subset _ X)), ?_, ?_⟩
                    · intro u hu w hw huw
                      rcases Finset.mem_insert.1 hu with rfl | hus <;>
                      rcases Finset.mem_insert.1 hw with rfl | hws
                      · exact False.elim (huw rfl)
                      · exact (Finset.mem_filter.1 (hsB hws)).2
                      · exact (Gᶜ.adj_comm _ _).1 (Finset.mem_filter.1 (hsB hus)).2
                      · exact hscl.1 hus hws huw
                    · have hv_not_s : v ∉ s := fun hvs => hv_not_B (hsB hvs)
                      rw [Finset.card_insert_of_notMem hv_not_s, hscl.card_eq]; omega
                  · exact Or.inr (Or.inr ⟨s, hsY'.trans (Finset.filter_subset _ Y), hscl⟩)
                · -- Both branches failed -> contradiction with (e:xx)!
                  exfalso
                  have hR_bound : αR / α * ((XR.card : ℝ) / (X.card : ℝ)) ≤
                      x ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) := by
                    by_cases hαR0 : αR ≤ 0
                    · have h1 : αR / α * ((XR.card : ℝ) / (X.card : ℝ)) ≤ 0 :=
                        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hαR0 hα_pos.le) (by positivity)
                      have h2 : 0 ≤ x ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) :=
                        by positivity
                      linarith
                    · have hαR_pos : 0 < αR := lt_of_not_ge hαR0
                      have hlt : αR ^ r * (XR.card : ℝ) < x * α ^ r * (X.card : ℝ) / (p - ε) := by
                        by_contra hge; exact hRstep ⟨hαR_pos.le, le_of_not_gt hge⟩
                      by_cases hXR0 : XR.card = 0
                      · simp [hXR0]; positivity
                      · have hXRpos : (0 : ℝ) < XR.card := by exact_mod_cast Nat.pos_of_ne_zero hXR0
                        have hdiv : (αR / α) ^ r ≤ x / (p - ε) * ((X.card : ℝ) / (XR.card : ℝ)) := by
                          rw [Real.div_rpow hαR_pos.le hα_pos.le, div_le_iff₀ (Real.rpow_pos_of_pos hα_pos r)]
                          have h1 := (le_div_iff₀ hXRpos).2 (show αR ^ r * (XR.card : ℝ) ≤ x * α ^ r * (X.card : ℝ) / (p - ε) from hlt.le)
                          calc αR ^ r ≤ x * α ^ r * (X.card : ℝ) / (p - ε) / (XR.card : ℝ) := h1
                            _ = x / (p - ε) * ((X.card : ℝ) / (XR.card : ℝ)) * α ^ r := by ring
                        have hpow := Real.rpow_le_rpow (by positivity) hdiv (div_nonneg zero_le_one hr0.le)
                        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hr0.ne', Real.rpow_one] at hpow
                        have hrhs_eq : (x / (p - ε) * ((X.card : ℝ) / (XR.card : ℝ))) ^ (1 / r) *
                            ((XR.card : ℝ) / (X.card : ℝ)) =
                            x ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) := by
                          rw [Real.mul_rpow (by positivity) (by positivity),
                              Real.div_rpow hx_pos.le (by linarith),
                              Real.div_rpow hXpos.le hXRpos.le,
                              Real.rpow_neg (by linarith : 0 ≤ p - ε),
                              Real.rpow_sub (div_pos hXRpos hXpos), Real.rpow_one,
                              Real.div_rpow hXRpos.le hXpos.le]
                          field_simp [(Real.rpow_pos_of_pos hXpos _).ne',
                            (Real.rpow_pos_of_pos hXRpos _).ne',
                            (Real.rpow_pos_of_pos (show 0 < p - ε by linarith) _).ne']
                        calc αR / α * ((XR.card : ℝ) / (X.card : ℝ))
                            ≤ (x / (p - ε) * ((X.card : ℝ) / (XR.card : ℝ))) ^ (1 / r) *
                                ((XR.card : ℝ) / (X.card : ℝ)) :=
                              mul_le_mul_of_nonneg_right hpow (by positivity)
                          _ = _ := hrhs_eq
                  have hB_bound : αB / α * ((XB.card : ℝ) / (X.card : ℝ)) ≤
                      μ ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) := by
                    by_cases hαB0 : αB ≤ 0
                    · have h1 : αB / α * ((XB.card : ℝ) / (X.card : ℝ)) ≤ 0 :=
                        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hαB0 hα_pos.le) (by positivity)
                      have h2 : 0 ≤ μ ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) :=
                        by positivity
                      linarith
                    · have hαB_pos : 0 < αB := lt_of_not_ge hαB0
                      have hlt : αB ^ r * (XB.card : ℝ) < μ * α ^ r * (X.card : ℝ) / (p - ε) := by
                        by_contra hge; exact hBstep ⟨hαB_pos.le, le_of_not_gt hge⟩
                      by_cases hXB0 : XB.card = 0
                      · simp [hXB0]; positivity
                      · have hXBpos : (0 : ℝ) < XB.card := by exact_mod_cast Nat.pos_of_ne_zero hXB0
                        have hdiv : (αB / α) ^ r ≤ μ / (p - ε) * ((X.card : ℝ) / (XB.card : ℝ)) := by
                          rw [Real.div_rpow hαB_pos.le hα_pos.le, div_le_iff₀ (Real.rpow_pos_of_pos hα_pos r)]
                          have h1 := (le_div_iff₀ hXBpos).2 (show αB ^ r * (XB.card : ℝ) ≤ μ * α ^ r * (X.card : ℝ) / (p - ε) from hlt.le)
                          calc αB ^ r ≤ μ * α ^ r * (X.card : ℝ) / (p - ε) / (XB.card : ℝ) := h1
                            _ = μ / (p - ε) * ((X.card : ℝ) / (XB.card : ℝ)) * α ^ r := by ring
                        have hpow := Real.rpow_le_rpow (by positivity) hdiv (div_nonneg zero_le_one hr0.le)
                        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hr0.ne', Real.rpow_one] at hpow
                        have hrhs_eq : (μ / (p - ε) * ((X.card : ℝ) / (XB.card : ℝ))) ^ (1 / r) *
                            ((XB.card : ℝ) / (X.card : ℝ)) =
                            μ ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) := by
                          rw [Real.mul_rpow (by positivity) (by positivity),
                              Real.div_rpow hμ_pos.le (by linarith),
                              Real.div_rpow hXpos.le hXBpos.le,
                              Real.rpow_neg (by linarith : 0 ≤ p - ε),
                              Real.rpow_sub (div_pos hXBpos hXpos), Real.rpow_one,
                              Real.div_rpow hXBpos.le hXpos.le]
                          field_simp [(Real.rpow_pos_of_pos hXpos _).ne',
                            (Real.rpow_pos_of_pos hXBpos _).ne',
                            (Real.rpow_pos_of_pos (show 0 < p - ε by linarith) _).ne']
                        calc αB / α * ((XB.card : ℝ) / (X.card : ℝ))
                            ≤ (μ / (p - ε) * ((X.card : ℝ) / (XB.card : ℝ))) ^ (1 / r) *
                                ((XB.card : ℝ) / (X.card : ℝ)) :=
                              mul_le_mul_of_nonneg_right hpow (by positivity)
                          _ = _ := hrhs_eq
                  -- Multiply by (p - ε)^(1/r) to get (e:moment3)
                  have hpr_pos : 0 < (p - ε) ^ (1 / r) := Real.rpow_pos_of_pos (by linarith) _
                  have hpr_cancel : (p - ε) ^ (-(1 / r)) * (p - ε) ^ (1 / r) = 1 := by
                    rw [← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero]
                  have hm3 : (p - ε) ^ (1 / r) ≤
                      x ^ (1 / r) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                      μ ^ (1 / r) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                      (p - ε) ^ (1 / r) / (α * (X.card : ℝ)) := by
                    have hsum := add_le_add (add_le_add hR_bound hB_bound) (le_rfl (a := 1 / (α * (X.card : ℝ))))
                    have hge1 : 1 ≤ x ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                        μ ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                        1 / (α * (X.card : ℝ)) := hmoment2.trans hsum
                    have hmul := mul_le_mul_of_nonneg_right hge1 hpr_pos.le
                    rw [one_mul] at hmul
                    have heq : (x ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                          μ ^ (1 / r) * (p - ε) ^ (-(1 / r)) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                          1 / (α * (X.card : ℝ))) * (p - ε) ^ (1 / r) =
                        x ^ (1 / r) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                        μ ^ (1 / r) * ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                        (p - ε) ^ (1 / r) / (α * (X.card : ℝ)) := by
                      calc _ = x ^ (1 / r) * ((p - ε) ^ (-(1 / r)) * (p - ε) ^ (1 / r)) *
                            ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                          μ ^ (1 / r) * ((p - ε) ^ (-(1 / r)) * (p - ε) ^ (1 / r)) *
                            ((XB.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                          (p - ε) ^ (1 / r) / (α * (X.card : ℝ)) := by ring
                        _ = _ := by rw [hpr_cancel, mul_one, mul_one]
                    linarith only [hmul, heq]
                  -- Use |XR|/|X| ≤ 1 - |XB|/|X| and monotonicity up to μ + ε ≤ μ / (μ + x)
                  set lam : ℝ := (XB.card : ℝ) / (X.card : ℝ)
                  have hXR_le_1lam : (XR.card : ℝ) / (X.card : ℝ) ≤ 1 - lam := by
                    dsimp [lam]
                    have h1 : (XR.card : ℝ) + (XB.card : ℝ) ≤ (X.card : ℝ) := by
                      have : (XR.card : ℝ) + (XB.card : ℝ) + 1 = (X.card : ℝ) := by exact_mod_cast hcard_part
                      linarith
                    rw [le_sub_iff_add_le, ← add_div, div_le_one hXpos]
                    exact h1
                  have hpos_exp : 0 < 1 - 1 / r := by
                    have : 1 / r < 1 := (div_lt_one hr0).2 hr1
                    linarith
                  have hXR_rpow : ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) ≤ (1 - lam) ^ (1 - 1 / r) :=
                    Real.rpow_le_rpow (by positivity) hXR_le_1lam hpos_exp.le
                  have hlam_le : lam ≤ μ + ε := (div_le_iff₀ hXpos).2 hXB_le.le
                  have hμ_frac : μ + ε ≤ μ / (μ + x) := by
                    have h1 : μ₀ / (μ₀ + 2 * ε + x₀) ≤ μ / (μ + x) := by
                      dsimp [μ, x]
                      rw [div_le_div_iff₀ (by linarith only [hμ0, hx0, hε_pos]) (by linarith only [hμ0, hx0, hε_pos])]
                      nlinarith only [hε_pos, hx0, hμ0]
                    have h2 : μ + ε = μ₀ + 2 * ε := by dsimp [μ]; ring
                    linarith
                  have hmono_r := rpow_sum_le_of_le hx_pos hμ_pos hr1 (by positivity : 0 ≤ lam)
                    hlam_le hμ_frac hμ_add_lt1
                  have h1μ_rpow : (1 - (μ + ε)) ^ (1 - 1 / r) ≤ (1 - μ) ^ (1 - 1 / r) :=
                    Real.rpow_le_rpow (by linarith) (by linarith) hpos_exp.le
                  have hμ_rpow : μ ^ (1 / r) * (μ + ε) ^ (1 - 1 / r) ≤ μ + ε := by
                    have h1 : μ ^ (1 / r) ≤ (μ + ε) ^ (1 / r) :=
                      Real.rpow_le_rpow hμ_pos.le (by linarith) (by positivity)
                    calc μ ^ (1 / r) * (μ + ε) ^ (1 - 1 / r)
                        ≤ (μ + ε) ^ (1 / r) * (μ + ε) ^ (1 - 1 / r) :=
                          mul_le_mul_of_nonneg_right h1 (by positivity)
                      _ = (μ + ε) ^ (1 / r + (1 - 1 / r)) :=
                          (Real.rpow_add (show 0 < μ + ε by linarith only [hμ_pos, hε_pos]) (1 / r) (1 - 1 / r)).symm
                      _ = μ + ε := by rw [add_sub_cancel, Real.rpow_one]
                  -- Bound the error term (p - ε)^(1/r) / (α * |X|) ≤ ε
                  have herr_le : (p - ε) ^ (1 / r) / (α * (X.card : ℝ)) ≤ ε := by
                    have hpr_le1 : (p - ε) ^ (1 / r) ≤ 1 :=
                      Real.rpow_le_one (by linarith) (by linarith) (by positivity)
                    have hkt2_le : ((k : ℝ) + t) ^ 2 ≤ (n : ℝ) ^ A_big := by
                      have h1 : ((k : ℝ) + t) ^ 2 ≤ (n : ℝ) ^ 2 :=
                        pow_le_pow_left₀ hkt_pos.le (by exact_mod_cast (show k + t ≤ n by omega)) 2
                      have h2 : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
                      have hA2 : (2 : ℝ) ≤ A_big := by dsimp [A_big]; linarith [le_max_right r 3]
                      exact h1.trans (h2.trans_le (Real.rpow_le_rpow_of_exponent_le
                        (by exact_mod_cast (show 1 ≤ n by omega)) hA2))
                    have hKε2 : ε⁻¹ ^ 2 ≤ K_const := by
                      have hle : ε⁻¹ ^ 2 ≤ max (max (ε⁻¹ ^ r) (ε⁻¹ ^ 2)) (max (5 * C_m ^ 2) (ε * (p - ε))⁻¹) :=
                        (le_max_right _ _).trans (le_max_left _ _)
                      dsimp [K_const]; linarith only [hle]
                    have hden_ge : ((k : ℝ) + t) ^ 2 ≤ ε ^ 2 * (X.card : ℝ) := by
                      have hexp1 : 1 ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) :=
                        Real.one_le_exp (by positivity)
                      have h1 : ε⁻¹ ^ 2 * ((k : ℝ) + t) ^ 2 ≤ (X.card : ℝ) := by
                        calc ε⁻¹ ^ 2 * ((k : ℝ) + t) ^ 2
                            ≤ K_const * ((n : ℝ) ^ A_big * Real.exp (B_big * (Real.log (n : ℝ)) ^ 3)) := by
                              have ha := mul_le_mul hKε2 hkt2_le (by positivity) hK_pos.le
                              exact ha.trans (by rw [← mul_assoc]; exact le_mul_of_one_le_right (by positivity) hexp1)
                          _ ≤ (1 + ε) ^ n := hL₀_pow n hn_ge_L₀
                          _ ≤ (X.card : ℝ) := hX_lb
                      have hmul := mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
                      have hcancel : ε ^ 2 * (ε⁻¹ ^ 2 * ((k : ℝ) + t) ^ 2) = ((k : ℝ) + t) ^ 2 := by
                        field_simp [hε_pos.ne']
                      linarith
                    rw [div_le_iff₀ (mul_pos hα_pos hXpos)]
                    have hαX : 1 ≤ ε * (α * (X.card : ℝ)) := by
                      have h1 : ε / ((k : ℝ) + t) ^ 2 * (X.card : ℝ) ≤ α * (X.card : ℝ) :=
                        mul_le_mul_of_nonneg_right hα_lb hXpos.le
                      have h2 : 1 ≤ ε * (ε / ((k : ℝ) + t) ^ 2 * (X.card : ℝ)) := by
                        have : ε * (ε / ((k : ℝ) + t) ^ 2 * (X.card : ℝ)) =
                            (ε ^ 2 * (X.card : ℝ)) / ((k : ℝ) + t) ^ 2 := by ring
                        rw [this, one_le_div (pow_pos hkt_pos 2)]
                        exact hden_ge
                      exact h2.trans (mul_le_mul_of_nonneg_left h1 hε_pos.le)
                    linarith
                  -- Combine into x^(1/r) (1 - μ)^(1 - 1/r) + μ + 2ε ≥ (p - ε)^(1/r), contradicting hε_rhs!
                  have hm4 : (p - ε) ^ (1 / r) - μ - 2 * ε ≤ x ^ (1 / r) * (1 - μ) ^ (1 - 1 / r) := by
                    have h1 : x ^ (1 / r) * ((XR.card : ℝ) / (X.card : ℝ)) ^ (1 - 1 / r) +
                        μ ^ (1 / r) * lam ^ (1 - 1 / r) ≤
                        x ^ (1 / r) * (1 - μ) ^ (1 - 1 / r) + (μ + ε) := by
                      calc _ ≤ x ^ (1 / r) * (1 - lam) ^ (1 - 1 / r) + μ ^ (1 / r) * lam ^ (1 - 1 / r) :=
                            add_le_add (mul_le_mul_of_nonneg_left hXR_rpow (Real.rpow_nonneg hx_pos.le _)) le_rfl
                        _ ≤ x ^ (1 / r) * (1 - (μ + ε)) ^ (1 - 1 / r) + μ ^ (1 / r) * (μ + ε) ^ (1 - 1 / r) :=
                            hmono_r
                        _ ≤ x ^ (1 / r) * (1 - μ) ^ (1 - 1 / r) + (μ + ε) :=
                            add_le_add (mul_le_mul_of_nonneg_left h1μ_rpow (Real.rpow_nonneg hx_pos.le _)) hμ_rpow
                    linarith
                  have hlhs_pos : 0 < (p - ε) ^ (1 / r) - μ - 2 * ε := by
                    dsimp [μ]; linarith
                  have hpow_r := Real.rpow_le_rpow hlhs_pos.le hm4 hr0.le
                  rw [Real.mul_rpow (by positivity) (by positivity),
                      ← Real.rpow_mul hx_pos.le, one_div_mul_cancel hr0.ne', Real.rpow_one,
                      ← Real.rpow_mul (by linarith : 0 ≤ 1 - μ)] at hpow_r
                  have hexp_mul : (1 - 1 / r) * r = r - 1 := by field_simp [hr0.ne']
                  rw [hexp_mul] at hpow_r
                  have hmul_inv := mul_le_mul_of_nonneg_right hpow_r
                    (Real.rpow_nonneg (show 0 ≤ 1 - μ by linarith) (1 - r))
                  have hcancel : x * (1 - μ) ^ (r - 1) * (1 - μ) ^ (1 - r) = x := by
                    rw [mul_assoc, ← Real.rpow_add (by linarith),
                        show (r - 1) + (1 - r) = 0 by ring, Real.rpow_zero, mul_one]
                  rw [hcancel] at hmul_inv
                  -- Compare with hε_rhs: x₀ < ((p-ε)^(1/r) - μ₀ - 3ε)^r * (1 - μ₀ - ε)^(1-r) - ε
                  have hμ_eq1 : (p - ε) ^ (1 / r) - μ - 2 * ε = (p - ε) ^ (1 / r) - μ₀ - 3 * ε := by
                    dsimp [μ]; ring
                  have hμ_eq2 : 1 - μ = 1 - μ₀ - ε := by dsimp [μ]; ring
                  rw [hμ_eq1, hμ_eq2] at hmul_inv
                  dsimp [x] at hmul_inv
                  linarith
        · -- Some v ∈ X has |N_R(v) ∩ Y| < (p - δkt) |Y|: delete v and apply ihX!
          push Not at hdeg_all
          obtain ⟨v, hvX, hv_small⟩ := hdeg_all
          set X' : Finset V := X.erase v
          have hX'card : X'.card < nX := by rw [← hXcard]; exact Finset.card_erase_lt_of_mem hvX
          have hX'ne : X'.Nonempty := by
            by_contra hemp
            have hX'e : X' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hemp
            have hXv : X = {v} := by
              ext u; constructor
              · intro hu
                by_cases huv : u = v
                · exact Finset.mem_singleton.2 huv
                · exfalso
                  have : u ∈ X' := Finset.mem_erase.2 ⟨huv, hu⟩
                  rw [hX'e] at this; exact Finset.notMem_empty u this
              · intro hu; rw [Finset.mem_singleton.1 hu]; exact hvX
            have heq : redEdges G X Y = (Y.filter (G.Adj v)).card := by
              rw [hXv, redEdges_eq_sum_card_filter, Finset.sum_singleton]
            have h1 : (p - δkt) * (Y.card : ℝ) ≤ (redEdges G X Y : ℝ) := by
              unfold dens at hdens_step
              have hXc1 : (X.card : ℝ) = 1 := by rw [hXv]; simp
              rw [hXc1, one_mul, le_div_iff₀ hYpos] at hdens_step
              exact hdens_step
            rw [heq] at h1
            linarith only [h1, hv_small]
          have hX'pos : (0 : ℝ) < X'.card := by exact_mod_cast hX'ne.card_pos
          have hX'c_eq : (X'.card : ℝ) + 1 = (X.card : ℝ) := by
            have := Finset.card_erase_add_one hvX
            exact_mod_cast this
          have heR_eq : (redEdges G X' Y : ℝ) + ((Y.filter (G.Adj v)).card : ℝ) = (redEdges G X Y : ℝ) := by
            exact_mod_cast redEdges_erase_left G hvX
          -- Excess increases: e_R(X', Y) - (p - δkt) |X'| |Y| > e_R(X, Y) - (p - δkt) |X| |Y|
          have hexcess_inc : (redEdges G X Y : ℝ) - (p - δkt) * ((X.card : ℝ) * (Y.card : ℝ)) ≤
              (redEdges G X' Y : ℝ) - (p - δkt) * ((X'.card : ℝ) * (Y.card : ℝ)) := by
            nlinarith only [hX'c_eq, heR_eq, hv_small]
          have hexcess_pos : 0 < (redEdges G X Y : ℝ) - (p - δkt) * ((X.card : ℝ) * (Y.card : ℝ)) := by
            have h1 : (dens G X Y + δkt - p) * ((X.card : ℝ) * (Y.card : ℝ)) =
                (redEdges G X Y : ℝ) - (p - δkt) * ((X.card : ℝ) * (Y.card : ℝ)) := by
              have hdm := dens_mul_cards G hXne hYne
              linarith only [hdm]
            rw [← h1]
            exact mul_pos hgap_pos (mul_pos hXpos hYpos)
          have hdens_inc : dens G X Y + δkt - p ≤ dens G X' Y + δkt - p := by
            have h1 : dens G X Y + δkt - p =
                ((redEdges G X Y : ℝ) - (p - δkt) * ((X.card : ℝ) * (Y.card : ℝ))) / ((X.card : ℝ) * (Y.card : ℝ)) := by
              have hdm := dens_mul_cards G hXne hYne
              rw [eq_div_iff (mul_pos hXpos hYpos).ne']; linarith only [hdm]
            have h2 : dens G X' Y + δkt - p =
                ((redEdges G X' Y : ℝ) - (p - δkt) * ((X'.card : ℝ) * (Y.card : ℝ))) / ((X'.card : ℝ) * (Y.card : ℝ)) := by
              have hdm := dens_mul_cards G hX'ne hYne
              rw [eq_div_iff (mul_pos hX'pos hYpos).ne']; linarith only [hdm]
            rw [h1, h2]
            have hXY_le : (X'.card : ℝ) * (Y.card : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by
              nlinarith only [hX'c_eq, hYpos]
            calc ((redEdges G X Y : ℝ) - (p - δkt) * ((X.card : ℝ) * (Y.card : ℝ))) / ((X.card : ℝ) * (Y.card : ℝ))
                ≤ ((redEdges G X' Y : ℝ) - (p - δkt) * ((X'.card : ℝ) * (Y.card : ℝ))) / ((X.card : ℝ) * (Y.card : ℝ)) :=
                  div_le_div_of_nonneg_right hexcess_inc (mul_pos hXpos hYpos).le
              _ ≤ ((redEdges G X' Y : ℝ) - (p - δkt) * ((X'.card : ℝ) * (Y.card : ℝ))) / ((X'.card : ℝ) * (Y.card : ℝ)) :=
                  div_le_div_of_nonneg_left (hexcess_pos.le.trans hexcess_inc) (mul_pos hX'pos hYpos) hXY_le
          have hdens_X' : p - δkt ≤ dens G X' Y := by linarith only [hdens_step, hdens_inc]
          have hmom_X' : (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤
              (dens G X' Y + δkt - p) ^ r * ((X'.card : ℝ) * (Y.card : ℝ)) := by
            have hfac_eq : ∀ (A : Finset V), A.Nonempty → 0 < dens G A Y + δkt - p →
                (dens G A Y + δkt - p) ^ r * ((A.card : ℝ) * (Y.card : ℝ)) =
                (dens G A Y + δkt - p) ^ (r - 1) *
                  ((redEdges G A Y : ℝ) - (p - δkt) * ((A.card : ℝ) * (Y.card : ℝ))) := by
              intro A hAne hApos
              have h1 : (dens G A Y + δkt - p) * ((A.card : ℝ) * (Y.card : ℝ)) =
                  (redEdges G A Y : ℝ) - (p - δkt) * ((A.card : ℝ) * (Y.card : ℝ)) := by
                have hdm := dens_mul_cards G hAne hYne; linarith only [hdm]
              rw [← h1]
              have hpow_eq : (dens G A Y + δkt - p) ^ (r - 1) * (dens G A Y + δkt - p) =
                  (dens G A Y + δkt - p) ^ r := by
                rw [← Real.rpow_add_one hApos.ne', sub_add_cancel]
              rw [← mul_assoc ((dens G A Y + δkt - p) ^ (r - 1)), hpow_eq]
            have hgap_X' : 0 < dens G X' Y + δkt - p := hgap_pos.trans_le hdens_inc
            have hpow_inc : (dens G X Y + δkt - p) ^ (r - 1) ≤ (dens G X' Y + δkt - p) ^ (r - 1) :=
              Real.rpow_le_rpow hgap_pos.le hdens_inc (by linarith only [hr1])
            have hmom_inc : (dens G X Y + δkt - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) ≤
                (dens G X' Y + δkt - p) ^ r * ((X'.card : ℝ) * (Y.card : ℝ)) := by
              rw [hfac_eq X hXne hgap_pos, hfac_eq X' hX'ne hgap_X']
              exact mul_le_mul hpow_inc hexcess_inc hexcess_pos.le
                (Real.rpow_nonneg hgap_X'.le _)
            exact hmom.trans hmom_inc
          have hX'good := ihX X'.card hX'card X' rfl hX'ne
            (Disjoint.mono_left (Finset.erase_subset v X) hdisj) hdens_X' hmom_X'
          rcases hX'good with ⟨s, hs, hscl⟩ | ⟨s, hs, hscl⟩ | ⟨s, hs, hscl⟩
          · exact Or.inl ⟨s, hs.trans (Finset.union_subset_union_left (Finset.erase_subset v X)), hscl⟩
          · exact Or.inr (Or.inl ⟨s, hs.trans (Finset.erase_subset v X), hscl⟩)
          · exact Or.inr (Or.inr ⟨s, hs, hscl⟩)
  -- Apply hind to the initial candidate (X, Y)
  have hkt_pos : (0 : ℝ) < (k : ℝ) + t := by positivity
  have hdens_init : p - ε / ((k : ℝ) + t) ≤ dens G X Y := by
    have : 0 ≤ ε / ((k : ℝ) + t) := by positivity
    linarith only [hdens, this]
  have hmom_init : (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹ ≤
      (dens G X Y + ε / ((k : ℝ) + t) - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) := by
    let n : ℕ := k + l + t
    have hn_ge_L₀ : L₀ ≤ n := hl.trans (by omega : l ≤ n)
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hgap : ε / ((k : ℝ) + t) ≤ dens G X Y + ε / ((k : ℝ) + t) - p := by linarith
    have h1 : (ε / ((k : ℝ) + t)) ^ r ≤ (dens G X Y + ε / ((k : ℝ) + t) - p) ^ r :=
      Real.rpow_le_rpow (by positivity) hgap hr0.le
    -- Show (1 + ε)^n ≥ ((k + t) / ε)^r
    have h2 : (((k : ℝ) + t) / ε) ^ r ≤ (1 + ε) ^ n := by
      have hkt_r : ((k : ℝ) + t) ^ r ≤ (n : ℝ) ^ A_big := by
        have h1 : ((k : ℝ) + t) ^ r ≤ (n : ℝ) ^ r :=
          Real.rpow_le_rpow hkt_pos.le (by exact_mod_cast (show k + t ≤ n by omega)) hr0.le
        have hAr : r ≤ A_big := by dsimp [A_big]; linarith [le_max_left r 3]
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hAr)
      have hKεr : ε⁻¹ ^ r ≤ K_const := by
        have hle : ε⁻¹ ^ r ≤ max (max (ε⁻¹ ^ r) (ε⁻¹ ^ 2)) (max (5 * C_m ^ 2) (ε * (p - ε))⁻¹) :=
          (le_max_left _ _).trans (le_max_left _ _)
        dsimp [K_const]; linarith only [hle]
      have hexp1 : 1 ≤ Real.exp (B_big * (Real.log (n : ℝ)) ^ 3) := by
        have hn4 : 4 ≤ n := (le_max_right _ _).trans hn_ge_L₀
        have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
        exact Real.one_le_exp (by positivity)
      calc (((k : ℝ) + t) / ε) ^ r
          = ε⁻¹ ^ r * ((k : ℝ) + t) ^ r := by
            rw [div_eq_mul_inv, Real.mul_rpow hkt_pos.le (inv_nonneg.2 hε_pos.le), mul_comm]
        _ ≤ K_const * ((n : ℝ) ^ A_big * Real.exp (B_big * (Real.log (n : ℝ)) ^ 3)) := by
            have ha := mul_le_mul hKεr hkt_r (by positivity) hK_pos.le
            exact ha.trans (by rw [← mul_assoc]; exact le_mul_of_one_le_right (by positivity) hexp1)
        _ ≤ (1 + ε) ^ n := hL₀_pow n hn_ge_L₀
    -- Also (x₀^k)⁻¹ (y₀^l)⁻¹ (μ₀^t)⁻¹ ≥ (1 + ε)^(k + l + t) * (x^k)⁻¹ (y^l)⁻¹ (μ^t)⁻¹
    have h3 : (1 + ε) ^ n * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹) ≤
        (x₀ ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ₀ ^ t)⁻¹ := by
      have hx1 : (1 + ε) ^ k * (x ^ k)⁻¹ ≤ (x₀ ^ k)⁻¹ := by
        have hpow : (1 + ε) ^ k * x₀ ^ k ≤ x ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hx_ratio k
        have := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (x ^ k)⁻¹ * (x₀ ^ k)⁻¹ by positivity)
        have hL : (1 + ε) ^ k * x₀ ^ k * ((x ^ k)⁻¹ * (x₀ ^ k)⁻¹) = (1 + ε) ^ k * (x ^ k)⁻¹ := by
          field_simp [(pow_pos hx0 k).ne', (pow_pos hx_pos k).ne']
        have hR : x ^ k * ((x ^ k)⁻¹ * (x₀ ^ k)⁻¹) = (x₀ ^ k)⁻¹ := by
          field_simp [(pow_pos hx0 k).ne', (pow_pos hx_pos k).ne']
        linarith
      have hy1 : (1 + ε) ^ l * (y ^ l)⁻¹ ≤ (y₀ ^ l)⁻¹ := by
        have hpow : (1 + ε) ^ l * y₀ ^ l ≤ y ^ l := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hy_ratio l
        have := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (y ^ l)⁻¹ * (y₀ ^ l)⁻¹ by positivity)
        have hL : (1 + ε) ^ l * y₀ ^ l * ((y ^ l)⁻¹ * (y₀ ^ l)⁻¹) = (1 + ε) ^ l * (y ^ l)⁻¹ := by
          field_simp [(pow_pos hy0 l).ne', (pow_pos hy_pos l).ne']
        have hR : y ^ l * ((y ^ l)⁻¹ * (y₀ ^ l)⁻¹) = (y₀ ^ l)⁻¹ := by
          field_simp [(pow_pos hy0 l).ne', (pow_pos hy_pos l).ne']
        linarith
      have hμ1' : (1 + ε) ^ t * (μ ^ t)⁻¹ ≤ (μ₀ ^ t)⁻¹ := by
        have hpow : (1 + ε) ^ t * μ₀ ^ t ≤ μ ^ t := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hμ_ratio t
        have := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (μ ^ t)⁻¹ * (μ₀ ^ t)⁻¹ by positivity)
        have hL : (1 + ε) ^ t * μ₀ ^ t * ((μ ^ t)⁻¹ * (μ₀ ^ t)⁻¹) = (1 + ε) ^ t * (μ ^ t)⁻¹ := by
          field_simp [(pow_pos hμ0 t).ne', (pow_pos hμ_pos t).ne']
        have hR : μ ^ t * ((μ ^ t)⁻¹ * (μ₀ ^ t)⁻¹) = (μ₀ ^ t)⁻¹ := by
          field_simp [(pow_pos hμ0 t).ne', (pow_pos hμ_pos t).ne']
        linarith
      have hmul := mul_le_mul (mul_le_mul hx1 hy1 (by positivity) (by positivity)) hμ1' (by positivity) (by positivity)
      dsimp [n]
      rw [pow_add, pow_add]
      linarith
    have hinv_r : (ε / ((k : ℝ) + t)) ^ r * (((k : ℝ) + t) / ε) ^ r = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have : ε / ((k : ℝ) + t) * (((k : ℝ) + t) / ε) = 1 := by
        field_simp [hε_pos.ne', hkt_pos.ne']
      rw [this, Real.one_rpow]
    calc (x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹
        = (ε / ((k : ℝ) + t)) ^ r * ((((k : ℝ) + t) / ε) ^ r * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹)) := by
          rw [← mul_assoc, hinv_r, one_mul]
      _ ≤ (ε / ((k : ℝ) + t)) ^ r * ((1 + ε) ^ n * ((x ^ k)⁻¹ * (y ^ l)⁻¹ * (μ ^ t)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      _ ≤ (ε / ((k : ℝ) + t)) ^ r * ((x₀ ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ₀ ^ t)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (dens G X Y + ε / ((k : ℝ) + t) - p) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) :=
          mul_le_mul h1 hXY (by positivity)
            (Real.rpow_nonneg (by linarith only [hgap, show (0 : ℝ) ≤ ε / ((k : ℝ) + t) by positivity]) r)
  exact hind (k + t) k t rfl hk ht X Y hXne hYne hdisj hdens_init hmom_init

/-- Averaging lemma: in a graph G on N ≥ 2 vertices with red edge density ≥ p
(i.e. ∑_{u ≠ v} 1_{G.Adj u v} ≥ p * N * (N - 1)), for m = N / 2 ≥ 1 there exist
disjoint subsets X, Y of size m with dens G X Y ≥ p. -/
lemma exists_disjoint_sets_dens_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ}
    (hN2 : 2 ≤ Fintype.card V)
    (hdens : p * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) ≤
      (∑ u : V, (Finset.univ.filter (G.Adj u)).card : ℝ)) :
    ∃ X Y : Finset V, X.card = Fintype.card V / 2 ∧ Y.card = Fintype.card V / 2 ∧
      Disjoint X Y ∧ p ≤ dens G X Y := by
  classical
  set N : ℕ := Fintype.card V
  set m : ℕ := N / 2
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m ≤ N := by omega
  -- Consider pairs (X, Y) with X ∈ powersetCard m univ, Y ∈ (univ \ X).powersetCard m
  let pairs : Finset (Finset V × Finset V) :=
    (Finset.univ.powersetCard m).biUnion fun X =>
      ((Finset.univ \ X).powersetCard m).image fun Y => (X, Y)
  have hpairs_mem : ∀ X Y : Finset V, (X, Y) ∈ pairs ↔
      X.card = m ∧ Y.card = m ∧ Disjoint X Y := by
    intro X Y
    simp only [pairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨X', hX'c, Y', ⟨hY'sub, hY'c⟩, rfl, rfl⟩
      refine ⟨hX'c, hY'c, ?_⟩
      rw [Finset.disjoint_left]
      intro v hvX hvY
      exact (Finset.mem_sdiff.1 (hY'sub hvY)).2 hvX
    · rintro ⟨hXc, hYc, hdisj⟩
      refine ⟨X, hXc, Y, ⟨?_, hYc⟩, rfl, rfl⟩
      intro v hvY
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun hvX => Finset.disjoint_left.1 hdisj hvX hvY⟩
  -- Count |pairs| = choose(N, m) * choose(N - m, m)
  have hpairs_card : pairs.card = Nat.choose N m * Nat.choose (N - m) m := by
    rw [Finset.card_biUnion]
    · calc ∑ X ∈ Finset.univ.powersetCard m, (((Finset.univ \ X).powersetCard m).image fun Y => (X, Y)).card
          = ∑ X ∈ Finset.univ.powersetCard m, Nat.choose (N - m) m := by
              refine Finset.sum_congr rfl fun X hX => ?_
              have hXc : X.card = m := (Finset.mem_powersetCard.1 hX).2
              rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
                  Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ X),
                  Finset.card_univ, hXc]
        _ = ((Finset.univ : Finset V).powersetCard m).card * Nat.choose (N - m) m := by simp
        _ = Nat.choose N m * Nat.choose (N - m) m := by
              rw [Finset.card_powersetCard, Finset.card_univ]
    · intro X₁ _ X₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rcases Finset.mem_image.1 hq1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.1 hq2 with ⟨_, _, h⟩
      exact hne (Prod.mk.inj h).1.symm
  -- For any distinct u, v : V, count pairs (X, Y) ∈ pairs with u ∈ X ∧ v ∈ Y
  have hcount_uv : ∀ u v : V, u ≠ v →
      (pairs.filter (fun q => u ∈ q.1 ∧ v ∈ q.2)).card =
      Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) := by
    intro u v huv
    let S0 : Finset V := Finset.univ \ {u, v}
    have hS0card : S0.card = N - 2 := by
      have hpair : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hpair]
    let dom : Finset (Finset V × Finset V) :=
      (S0.powersetCard (m - 1)).biUnion fun A =>
        ((S0 \ A).powersetCard (m - 1)).image fun B => (A, B)
    have hdom_card : dom.card = Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) := by
      rw [Finset.card_biUnion]
      · calc ∑ A ∈ S0.powersetCard (m - 1), (((S0 \ A).powersetCard (m - 1)).image fun B => (A, B)).card
            = ∑ A ∈ S0.powersetCard (m - 1), Nat.choose (N - m - 1) (m - 1) := by
                refine Finset.sum_congr rfl fun A hA => ?_
                have hAsub : A ⊆ S0 := (Finset.mem_powersetCard.1 hA).1
                have hAc : A.card = m - 1 := (Finset.mem_powersetCard.1 hA).2
                rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
                    Finset.card_powersetCard, Finset.card_sdiff_of_subset hAsub, hS0card, hAc]
                have : N - 2 - (m - 1) = N - m - 1 := by omega
                rw [this]
          _ = (S0.powersetCard (m - 1)).card * Nat.choose (N - m - 1) (m - 1) := by simp
          _ = Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) := by
                rw [Finset.card_powersetCard, hS0card]
      · intro A₁ _ A₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        rcases Finset.mem_image.1 hq1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.1 hq2 with ⟨_, _, h⟩
        exact hne (Prod.mk.inj h).1.symm
    rw [← hdom_card]
    refine Finset.card_bij (fun q _ => (q.1.erase u, q.2.erase v)) ?_ ?_ ?_
    · intro q hq
      rcases Finset.mem_filter.1 hq with ⟨hqP, huq, hvq⟩
      rcases (hpairs_mem q.1 q.2).1 hqP with ⟨h1c, h2c, hdisj⟩
      simp only [dom, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powersetCard]
      refine ⟨q.1.erase u, ⟨?_, by rw [Finset.card_erase_of_mem huq, h1c]⟩,
        q.2.erase v, ⟨?_, by rw [Finset.card_erase_of_mem hvq, h2c]⟩, rfl⟩
      · intro w hw
        rcases Finset.mem_erase.1 hw with ⟨hwu, hw1⟩
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ w, fun hwp => ?_⟩
        rcases Finset.mem_insert.1 hwp with rfl | hwp2
        · exact hwu rfl
        · rw [Finset.mem_singleton.1 hwp2] at hw1
          exact Finset.disjoint_left.1 hdisj hw1 hvq
      · intro w hw
        rcases Finset.mem_erase.1 hw with ⟨hwv, hw2⟩
        refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ w, fun hwp => ?_⟩, fun hw1 => ?_⟩
        · rcases Finset.mem_insert.1 hwp with rfl | hwp2
          · exact Finset.disjoint_left.1 hdisj huq hw2
          · exact hwv (Finset.mem_singleton.1 hwp2)
        · exact Finset.disjoint_left.1 hdisj (Finset.mem_erase.1 hw1).2 hw2
    · intro q₁ hq₁ q₂ hq₂ heq
      rcases Finset.mem_filter.1 hq₁ with ⟨_, hu₁, hv₁⟩
      rcases Finset.mem_filter.1 hq₂ with ⟨_, hu₂, hv₂⟩
      rcases Prod.mk.inj heq with ⟨he1, he2⟩
      apply Prod.ext
      · rw [← Finset.insert_erase hu₁, ← Finset.insert_erase hu₂, he1]
      · rw [← Finset.insert_erase hv₁, ← Finset.insert_erase hv₂, he2]
    · intro ab hab
      simp only [dom, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powersetCard] at hab
      rcases hab with ⟨A, ⟨hAS0, hAc⟩, B, ⟨hBS0A, hBc⟩, rfl⟩
      have huA : u ∉ A := fun h => (Finset.mem_sdiff.1 (hAS0 h)).2 (Finset.mem_insert_self u {v})
      have hvA : v ∉ A := fun h => (Finset.mem_sdiff.1 (hAS0 h)).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
      have huB : u ∉ B := fun h => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 (hBS0A h)).1).2 (Finset.mem_insert_self u {v})
      have hvB : v ∉ B := fun h => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 (hBS0A h)).1).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
      refine ⟨(insert u A, insert v B), ?_, ?_⟩
      · refine Finset.mem_filter.2 ⟨(hpairs_mem _ _).2 ⟨?_, ?_, ?_⟩,
          Finset.mem_insert_self u A, Finset.mem_insert_self v B⟩
        · rw [Finset.card_insert_of_notMem huA, hAc]; omega
        · rw [Finset.card_insert_of_notMem hvB, hBc]; omega
        · rw [Finset.disjoint_left]
          intro w hw1 hw2
          rcases Finset.mem_insert.1 hw1 with rfl | hwA <;>
          rcases Finset.mem_insert.1 hw2 with rfl | hwB
          · exact huv rfl
          · exact huB hwB
          · exact hvA hwA
          · exact (Finset.mem_sdiff.1 (hBS0A hwB)).2 hwA
      · ext <;> simp [Finset.erase_insert huA, Finset.erase_insert hvB]
  -- Double count ∑_{q ∈ pairs} redEdges G q.1 q.2
  have hdouble : ∑ q ∈ pairs, redEdges G q.1 q.2 =
      (Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1)) *
      (∑ u : V, (Finset.univ.filter (G.Adj u)).card) := by
    calc ∑ q ∈ pairs, redEdges G q.1 q.2
        = ∑ q ∈ pairs, ∑ u : V, ∑ v : V, if u ∈ q.1 ∧ v ∈ q.2 ∧ G.Adj u v then 1 else 0 := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [redEdges_eq_sum_card_filter]
            symm
            calc ∑ u : V, ∑ v : V, (if u ∈ q.1 ∧ v ∈ q.2 ∧ G.Adj u v then 1 else 0)
                = ∑ u : V, if u ∈ q.1 then (∑ v : V, if v ∈ q.2 then (if G.Adj u v then 1 else 0) else 0) else 0 := by
                    refine Finset.sum_congr rfl fun u _ => ?_
                    by_cases hu : u ∈ q.1
                    · simp only [hu, true_and, if_true]
                      refine Finset.sum_congr rfl fun v _ => by by_cases hv : v ∈ q.2 <;> simp [hv]
                    · simp [hu]
              _ = ∑ u ∈ q.1, ∑ v ∈ q.2, if G.Adj u v then 1 else 0 := by
                    rw [Finset.sum_ite_mem, Finset.univ_inter]
                    refine Finset.sum_congr rfl fun u _ => ?_
                    rw [Finset.sum_ite_mem, Finset.univ_inter]
              _ = ∑ u ∈ q.1, (q.2.filter (G.Adj u)).card := by
                    refine Finset.sum_congr rfl fun u _ => (Finset.card_filter _ _).symm
      _ = ∑ u : V, ∑ v : V, ∑ q ∈ pairs, if u ∈ q.1 ∧ v ∈ q.2 ∧ G.Adj u v then 1 else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u : V, ∑ v : V, if G.Adj u v then
            Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) else 0 := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            by_cases hadj : G.Adj u v
            · simp only [hadj, and_true, if_true]
              rw [← Finset.card_filter]
              exact hcount_uv u v (G.ne_of_adj hadj)
            · simp [hadj]
      _ = (Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1)) *
          ∑ u : V, (Finset.univ.filter (G.Adj u)).card := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.card_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  -- Identity: m^2 * choose(N, m) * choose(N - m, m) = N * (N - 1) * choose(N - 2, m - 1) * choose(N - m - 1, m - 1)
  have hbinom_id : m * m * (Nat.choose N m * Nat.choose (N - m) m) =
      N * (N - 1) * (Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1)) := by
    have h1 : N * Nat.choose (N - 1) (m - 1) = Nat.choose N m * m := by
      have := Nat.add_one_mul_choose_eq (N - 1) (m - 1)
      have hN1 : N - 1 + 1 = N := by omega
      have hm1' : m - 1 + 1 = m := by omega
      rw [hN1, hm1'] at this
      linarith
    have h2 : (N - 1) * Nat.choose (N - 2) (m - 1) = Nat.choose (N - 1) (m - 1) * (N - m) := by
      have := Nat.choose_mul_succ_eq (N - 2) (m - 1)
      -- Alternatively: (N - 1) * choose(N - 2, m - 1) = (N - m) * choose(N - 1, m - 1)
      -- Use Nat.choose_succ_right_eq or direct: choose(n+1, k) * (n + 1 - k) = (n + 1) * choose(n, k)
      have h3 : Nat.choose (N - 1) (m - 1) * (N - m) =
          Nat.choose (N - 2) (m - 1) * (N - 1) := by
        have hstep := Nat.choose_mul_succ_eq (N - 1) (N - m - 1)
        -- Simpler: use factorial identity!
        have hle1 : m - 1 ≤ N - 2 := by omega
        have hle2 : m - 1 ≤ N - 1 := by omega
        have hsub1 : (N - 2) - (m - 1) = N - m - 1 := by omega
        have hsub2 : (N - 1) - (m - 1) = N - m := by omega
        have hfac1 := Nat.choose_mul_factorial_mul_factorial hle1
        have hfac2 := Nat.choose_mul_factorial_mul_factorial hle2
        rw [hsub1] at hfac1; rw [hsub2] at hfac2
        have hNf : (N - 1).factorial = (N - 1) * (N - 2).factorial := by
          have : N - 1 = (N - 2) + 1 := by omega
          conv_lhs => rw [this, Nat.factorial_succ]
          rw [← this]
        have hNmf : (N - m).factorial = (N - m) * (N - m - 1).factorial := by
          have : N - m = (N - m - 1) + 1 := by omega
          conv_lhs => rw [this, Nat.factorial_succ]
          rw [← this]
        have hmul : (Nat.choose (N - 1) (m - 1) * (N - m)) * ((m - 1).factorial * (N - m - 1).factorial) =
            (Nat.choose (N - 2) (m - 1) * (N - 1)) * ((m - 1).factorial * (N - m - 1).factorial) := by
          calc _ = Nat.choose (N - 1) (m - 1) * (m - 1).factorial * ((N - m) * (N - m - 1).factorial) := by ring
            _ = (N - 1).factorial := by rw [← hNmf, hfac2]
            _ = (N - 1) * (N - 2).factorial := hNf
            _ = (N - 1) * (Nat.choose (N - 2) (m - 1) * (m - 1).factorial * (N - m - 1).factorial) := by rw [hfac1]
            _ = _ := by ring
        exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) hmul
      linarith
    have h3 : (N - m) * Nat.choose (N - m - 1) (m - 1) = Nat.choose (N - m) m * m := by
      have := Nat.add_one_mul_choose_eq (N - m - 1) (m - 1)
      have h1' : N - m - 1 + 1 = N - m := by omega
      have h2' : m - 1 + 1 = m := by omega
      rw [h1', h2'] at this
      linarith
    have hNm_pos : 0 < N - m := by omega
    apply Nat.eq_of_mul_eq_mul_left hNm_pos
    calc (N - m) * (m * m * (Nat.choose N m * Nat.choose (N - m) m))
        = (N - m) * (Nat.choose N m * m) * (Nat.choose (N - m) m * m) := by ring
      _ = (N - m) * (N * Nat.choose (N - 1) (m - 1)) * ((N - m) * Nat.choose (N - m - 1) (m - 1)) := by
          rw [← h1, ← h3]
      _ = (N - m) * (N * ((N - 1) * Nat.choose (N - 2) (m - 1))) * Nat.choose (N - m - 1) (m - 1) := by
          have : (N - m) * (N * Nat.choose (N - 1) (m - 1)) = N * (Nat.choose (N - 1) (m - 1) * (N - m)) := by ring
          rw [this, ← h2]; ring
      _ = (N - m) * (N * (N - 1) * (Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1))) := by ring
  -- Now average over pairs:
  have hpairs_pos : 0 < pairs.card := by
    rw [hpairs_card]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hpairs_ne : pairs.Nonempty := Finset.card_pos.1 hpairs_pos
  have hsum_ge : (pairs.card : ℝ) * p ≤ ∑ q ∈ pairs, dens G q.1 q.2 := by
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsum_dens : ∑ q ∈ pairs, dens G q.1 q.2 =
        (∑ q ∈ pairs, (redEdges G q.1 q.2 : ℝ)) / ((m : ℝ) * (m : ℝ)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q hq => ?_
      rcases (hpairs_mem q.1 q.2).1 hq with ⟨h1c, h2c, _⟩
      unfold dens; rw [h1c, h2c]
    rw [hsum_dens, le_div_iff₀ (mul_pos hm_pos hm_pos)]
    have hdouble_r : ∑ q ∈ pairs, (redEdges G q.1 q.2 : ℝ) =
        ((Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) : ℕ) : ℝ) *
        (∑ u : V, (Finset.univ.filter (G.Adj u)).card : ℝ) := by
      exact_mod_cast hdouble
    have hbinom_r : ((m : ℝ) * (m : ℝ)) * (pairs.card : ℝ) =
        (N : ℝ) * ((N : ℝ) - 1) * ((Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) : ℕ) : ℝ) := by
      rw [hpairs_card]
      have hcast : ((m * m * (Nat.choose N m * Nat.choose (N - m) m) : ℕ) : ℝ) =
          ((N * (N - 1) * (Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1)) : ℕ) : ℝ) := by
        exact_mod_cast hbinom_id
      push_cast [Nat.cast_sub (show 1 ≤ N by omega)] at hcast ⊢
      exact hcast
    rw [hdouble_r]
    calc (pairs.card : ℝ) * p * ((m : ℝ) * (m : ℝ))
        = p * (((m : ℝ) * (m : ℝ)) * (pairs.card : ℝ)) := by ring
      _ = ((Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) : ℕ) : ℝ) *
          (p * ((N : ℝ) * ((N : ℝ) - 1))) := by rw [hbinom_r]; ring
      _ ≤ ((Nat.choose (N - 2) (m - 1) * Nat.choose (N - m - 1) (m - 1) : ℕ) : ℝ) *
          (∑ u : V, (Finset.univ.filter (G.Adj u)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hdens (Nat.cast_nonneg _)
  obtain ⟨q, hqmem, hqmax⟩ := Finset.exists_max_image pairs (fun q => dens G q.1 q.2) hpairs_ne
  have hqp : p ≤ dens G q.1 q.2 := by
    have hub : ∑ q' ∈ pairs, dens G q'.1 q'.2 ≤ (pairs.card : ℝ) * dens G q.1 q.2 := by
      calc ∑ q' ∈ pairs, dens G q'.1 q'.2
          ≤ ∑ _q' ∈ pairs, dens G q.1 q.2 := Finset.sum_le_sum fun q' hq' => hqmax q' hq'
        _ = (pairs.card : ℝ) * dens G q.1 q.2 := by simp
    exact le_of_mul_le_mul_left (hsum_ge.trans hub) (by exact_mod_cast hpairs_pos)
  rcases (hpairs_mem q.1 q.2).1 hqmem with ⟨h1c, h2c, hdisj⟩
  exact ⟨q.1, q.2, h1c, h2c, hdisj, hqp⟩

/-- Theorem 13 in GNNW (`t:bookCor`):
For 0 < μ, x, y, p < 1 with x < p^(1/(1-μ)) * (1 - μ) and (x, y) in the interior of R,
there exists L₀ such that for all k ≥ 1, l ≥ L₀, every graph G on N ≥ x^{-k/2} (μ y)^{-l/2}
vertices with red edge density ≥ p contains a red K_k or a blue K_l. -/
theorem book_cor {μ x y p : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (_hy1 : y < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hxp : x < p ^ (1 / (1 - μ)) * (1 - μ))
    (hR : ∃ x₁ y₁ : ℝ, x < x₁ ∧ y < y₁ ∧ InR x₁ y₁) :
    ∃ L₀ : ℕ, ∀ (N k l : ℕ), 1 ≤ k → L₀ ≤ l →
      (x ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ * y) ^ l)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) →
      ∀ G : SimpleGraph (Fin N), [DecidableRel G.Adj] →
      p * ((N : ℝ) * ((N : ℝ) - 1)) ≤ (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ) →
      (∃ s : Finset (Fin N), G.IsNClique k s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique l s) := by
  obtain ⟨x₁, y₁, hx_lt, hy_lt, hInR⟩ := hR
  let y₀ : ℝ := (y + y₁) / 2
  have hy₀_gt : y < y₀ := by dsimp [y₀]; linarith
  have hy₀_lt : y₀ < y₁ := by dsimp [y₀]; linarith
  have hy₀_pos : 0 < y₀ := hy0.trans hy₀_gt
  have hy₀_lt1 : y₀ < 1 := hy₀_lt.trans hInR.2.2.2.1
  obtain ⟨L₁, hL₁⟩ := book_main hμ0 hμ1 hx0 hx1 hy₀_pos hy₀_lt1 hp0 hp1 hxp ⟨x₁, y₁, hx_lt, hy₀_lt, hInR⟩
  -- Choose L₂ so that (y₀ / y)^(l/2) ≥ 3 for all l ≥ L₂
  have hrat : 1 < y₀ / y := (one_lt_div hy0).2 hy₀_gt
  have hlog_rat : 0 < Real.log (y₀ / y) := Real.log_pos hrat
  obtain ⟨L₂, hL₂⟩ := exists_nat_gt (2 * Real.log 3 / Real.log (y₀ / y))
  refine ⟨max (max L₁ L₂) 1, fun N k l hk hl hN G _ hdens => ?_⟩
  have hl1 : L₁ ≤ l := ((le_max_left L₁ L₂).trans (le_max_left _ 1)).trans hl
  have hl2 : L₂ ≤ l := ((le_max_right L₁ L₂).trans (le_max_left _ 1)).trans hl
  have hl_pos : 1 ≤ l := (le_max_right _ 1).trans hl
  have h3_le : (3 : ℝ) ≤ (y₀ / y) ^ ((l : ℝ) / 2) := by
    have hlt : 2 * Real.log 3 / Real.log (y₀ / y) < (l : ℝ) := hL₂.trans_le (by exact_mod_cast hl2)
    have hmul : Real.log 3 < ((l : ℝ) / 2) * Real.log (y₀ / y) := by
      have := (div_lt_iff₀ hlog_rat).1 hlt; linarith
    rw [Real.rpow_def_of_pos (div_pos hy₀_pos hy0)]
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (y₀ / y) * ((l : ℝ) / 2)) := Real.exp_le_exp.2 (by linarith)
  set A : ℝ := (x ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2)
  have hA_ge1 : 1 ≤ A := by
    have h1 : 1 ≤ (x ^ k)⁻¹ := (one_le_inv₀ (pow_pos hx0 k)).2 (pow_le_one₀ hx0.le hx1.le)
    have h2 : 1 ≤ ((μ * y₀) ^ l)⁻¹ :=
      (one_le_inv₀ (pow_pos (mul_pos hμ0 hy₀_pos) l)).2 (pow_le_one₀ (by positivity) (by nlinarith))
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 (by norm_num)) (Real.one_le_rpow h2 (by norm_num))
  have hN_ge_3A : 3 * A ≤ (N : ℝ) := by
    have hratio_eq : (x ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ * y) ^ l)⁻¹ ^ ((1 : ℝ) / 2) =
        (y₀ / y) ^ ((l : ℝ) / 2) * A := by
      dsimp [A]
      have hy_eq : ((μ * y) ^ l)⁻¹ ^ ((1 : ℝ) / 2) = (y₀ / y) ^ ((l : ℝ) / 2) * ((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (div_pos hy₀_pos hy0),
            Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
        congr 1
        rw [Real.log_inv, Real.log_inv, Real.log_pow, Real.log_pow,
            Real.log_mul hμ0.ne' hy0.ne', Real.log_mul hμ0.ne' hy₀_pos.ne',
            Real.log_div hy₀_pos.ne' hy0.ne']
        ring
      rw [hy_eq]; ring
    rw [hratio_eq] at hN
    exact (mul_le_mul_of_nonneg_right h3_le (by linarith)).trans hN
  have hN2 : 2 ≤ N := by
    have : (3 : ℝ) ≤ (N : ℝ) := by linarith
    have : 3 ≤ N := by exact_mod_cast this
    omega
  obtain ⟨X, Y, hXc, hYc, hdisj, hdXY⟩ := exists_disjoint_sets_dens_ge G (by simpa using hN2) (by simpa using hdens)
  have hXc' : X.card = N / 2 := by simpa using hXc
  have hYc' : Y.card = N / 2 := by simpa using hYc
  have hm_ge_A : A ≤ ((N / 2 : ℕ) : ℝ) := by
    have hdiv : (N : ℝ) - 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) := by
      have : N - 1 ≤ 2 * (N / 2) := by omega
      have : ((N - 1 : ℕ) : ℝ) ≤ ((2 * (N / 2) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at this
      exact this
    linarith
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  have hYne : Y.Nonempty := Finset.card_pos.1 (by omega)
  have hXY_ge : (x ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ ^ l)⁻¹ ≤ (X.card : ℝ) * (Y.card : ℝ) := by
    have hA2 : A * A = (x ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ ^ l)⁻¹ := by
      dsimp [A]
      have h1 : (x ^ k)⁻¹ ^ ((1 : ℝ) / 2) * (x ^ k)⁻¹ ^ ((1 : ℝ) / 2) = (x ^ k)⁻¹ := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      have h2 : ((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2) * ((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2) = ((μ * y₀) ^ l)⁻¹ := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      calc A * A = ((x ^ k)⁻¹ ^ ((1 : ℝ) / 2) * (x ^ k)⁻¹ ^ ((1 : ℝ) / 2)) *
            (((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2) * ((μ * y₀) ^ l)⁻¹ ^ ((1 : ℝ) / 2)) := by ring
        _ = (x ^ k)⁻¹ * ((μ * y₀) ^ l)⁻¹ := by rw [h1, h2]
        _ = (x ^ k)⁻¹ * (y₀ ^ l)⁻¹ * (μ ^ l)⁻¹ := by rw [mul_pow, mul_inv]; ring
    rw [← hA2, hXc', hYc']
    exact mul_le_mul hm_ge_A hm_ge_A (by linarith) (by linarith)
  have hgood := hL₁ (Fin N) G k l l hk hl1 hl_pos X Y hXne hYne hdisj hdXY hXY_ge
  rcases hgood with ⟨s, _, hscl⟩ | ⟨s, _, hscl⟩ | ⟨s, _, hscl⟩
  · exact Or.inl ⟨s, hscl⟩
  · exact Or.inr ⟨s, hscl⟩
  · exact Or.inr ⟨s, hscl⟩

end Erdos627AFM

/- ==================== Section: DescentFrontier.lean ====================-/
namespace Erdos627AFM

open SimpleGraph Finset Real Set Filter Topology

/-- Helper: binary entropy h(λ) = (1 + λ) log(1 + λ) - λ log λ. -/
noncomputable def hEnt (lam : ℝ) : ℝ :=
  (1 + lam) * Real.log (1 + lam) - lam * Real.log lam

lemma hEnt_eq_binEntropy {lam : ℝ} (hlam : 0 < lam) :
    hEnt lam = (1 + lam) * Real.binEntropy (lam / (1 + lam)) := by
  have h1 : 0 < 1 + lam := by linarith
  have hsub : 1 - lam / (1 + lam) = 1 / (1 + lam) := by field_simp; ring
  unfold hEnt Real.binEntropy
  rw [hsub, inv_div, one_div, inv_inv, Real.log_div h1.ne' hlam.ne']
  field_simp [h1.ne']
  ring

/-- Small-ratio Erdős-Szekeres bound: for any ε > 0 there exists ε' ∈ (0, 1/2) such that
for all k ≥ 1 and 1 ≤ l ≤ ε' * k, R(k, l) ≤ exp(ε * k). -/
lemma small_ratio_ramsey {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' < 1 / 2 ∧
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → (l : ℝ) ≤ ε' * (k : ℝ) →
        (ramsey k l : ℝ) ≤ Real.exp (ε * (k : ℝ)) := by
  let ε' : ℝ := min (1 / 4) ((ε / 6) ^ 2)
  have hε'0 : 0 < ε' := by dsimp [ε']; positivity
  have hε'1 : ε' < 1 / 2 := by dsimp [ε']; linarith [min_le_left (1 / 4 : ℝ) ((ε / 6) ^ 2)]
  refine ⟨ε', hε'0, hε'1, fun k l hk hl hle => ?_⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hl_pos : (0 : ℝ) < l := by exact_mod_cast hl
  set lam : ℝ := (l : ℝ) / (k : ℝ)
  have hlam0 : 0 < lam := div_pos hl_pos hk_pos
  have hlam_le : lam ≤ ε' := (div_le_iff₀ hk_pos).2 hle
  have hlam1 : lam ≤ 1 := by linarith
  have hEnt_lt : hEnt lam < ε := by
    unfold hEnt
    have hlog1 : Real.log (1 + lam) ≤ lam := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + lam by linarith)]
    have h1t : (1 + lam) * Real.log (1 + lam) ≤ 2 * lam := by
      have hlog_nn : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
      nlinarith
    have hlog_inv : -Real.log lam ≤ 2 * lam ^ (-(1 : ℝ) / 2) := by
      have hpow_pos : 0 < lam ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hlam0 _
      have hstep := Real.log_le_sub_one_of_pos hpow_pos
      rw [Real.log_rpow hlam0] at hstep
      linarith
    have hneg : -lam * Real.log lam ≤ 2 * Real.sqrt lam := by
      calc -lam * Real.log lam = lam * (-Real.log lam) := by ring
        _ ≤ lam * (2 * lam ^ (-(1 : ℝ) / 2)) := mul_le_mul_of_nonneg_left hlog_inv hlam0.le
        _ = 2 * (lam ^ (1 : ℝ) * lam ^ (-(1 : ℝ) / 2)) := by rw [Real.rpow_one]; ring
        _ = 2 * lam ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_add hlam0]; norm_num
        _ = 2 * Real.sqrt lam := by rw [Real.sqrt_eq_rpow]
    have hlam_sq : lam ≤ Real.sqrt lam := by
      have h1 : lam ^ 2 ≤ lam := by nlinarith
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq hlam0.le] at h2
    have hsqrt_le : Real.sqrt lam ≤ ε / 6 := by
      have h1 : lam ≤ (ε / 6) ^ 2 := hlam_le.trans (min_le_right _ _)
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h2
    linarith
  have hch1 : (ramsey k l : ℝ) ≤ (Nat.choose (k + l) l : ℝ) := by
    have h1 : ramsey k l ≤ Nat.choose (k + l - 2) (k - 1) := ramsey_le_choose hk hl
    have h2 : Nat.choose (k + l - 2) (k - 1) ≤ Nat.choose (k + l) (k - 1) :=
      Nat.choose_le_choose (k - 1) (by omega)
    have h3 : Nat.choose (k + l - 2) (k - 1) ≤ Nat.choose (k + l) l := by
      have hsym : Nat.choose (k + l - 2) (k - 1) = Nat.choose (k + l - 2) (l - 1) := by
        have hsub : k + l - 2 - (k - 1) = l - 1 := by omega
        rw [← Nat.choose_symm (by omega : k - 1 ≤ k + l - 2), hsub]
      rw [hsym]
      calc Nat.choose (k + l - 2) (l - 1)
          ≤ Nat.choose (k + l - 1) l := by
            have heq : k + l - 1 = (k + l - 2) + 1 := by omega
            have heq2 : l = (l - 1) + 1 := by omega
            rw [heq, heq2, Nat.choose_succ_succ]
            exact Nat.le_add_right _ _
        _ ≤ Nat.choose (k + l) l := Nat.choose_le_choose l (by omega)
    exact_mod_cast h1.trans h3
  have hch2 : (Nat.choose (k + l) l : ℝ) ≤
      Real.exp (((l : ℝ) + (k : ℝ)) * Real.binEntropy ((l : ℝ) / ((l : ℝ) + (k : ℝ)))) := by
    have := choose_le_exp_binEntropy hl hk
    rwa [Nat.add_comm l k] at this
  have harg : (l : ℝ) / ((l : ℝ) + (k : ℝ)) = lam / (1 + lam) := by
    dsimp [lam]; field_simp [hk_pos.ne']; ring
  have hexp_eq : ((l : ℝ) + (k : ℝ)) * Real.binEntropy ((l : ℝ) / ((l : ℝ) + (k : ℝ))) =
      hEnt lam * (k : ℝ) := by
    rw [harg, hEnt_eq_binEntropy hlam0]
    have h1 : (l : ℝ) + (k : ℝ) = (1 + lam) * (k : ℝ) := by dsimp [lam]; field_simp [hk_pos.ne']; ring
    rw [h1]; ring
  rw [hexp_eq] at hch2
  exact hch1.trans (hch2.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hEnt_lt.le hk_pos.le)))

set_option maxHeartbeats 800000 in
/-- Theorem 14 in GNNW (`t:general`):
Given C^1 function F : (0, 1] → ℝ₊ with F' > 0, continuous M : (0, 1] → (0, 1),
such that for every λ ∈ (0, 1] there exists y ∈ (0, 1) with (X(λ), y) ∈ InR and
-(log X(λ) + λ log M(λ) + λ log y)/2 < F(λ), where X(λ) = (1 - exp(-F'(λ)))^(1/(1-M(λ))) * (1 - M(λ)),
we obtain R(k, l) ≤ exp((F(l/k) + ε) * k) for all sufficiently large k and 1 ≤ l ≤ k. -/
theorem general_ramsey_bound_aux
    (F F' M : ℝ → ℝ)
    (hF_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ F t)
    (hF_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'_cont : ContinuousOn F' (Ioc 0 1))
    (hF'_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < F' t)
    (hM_cont : ContinuousOn M (Ioc 0 1))
    (hM_mem : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < M t ∧ M t < 1)
    (hcond : ∀ t ∈ Ioc (0 : ℝ) 1, ∃ y : ℝ, 0 < y ∧ y < 1 ∧
      let X := (1 - Real.exp (-F' t)) ^ (1 / (1 - M t)) * (1 - M t)
      InR X y ∧
      -(Real.log X + t * Real.log (M t) + t * Real.log y) / 2 < F t) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) + 1 := by
  intro ε hε
  obtain ⟨ε', hε'0, hε'1, hsmall⟩ := small_ratio_ramsey hε
  -- Work on compact interval I = [ε'/2, 1]
  have hI_sub : Icc (ε' / 2) 1 ⊆ Ioc 0 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hI_comp : IsCompact (Icc (ε' / 2) 1) := isCompact_Icc
  have hI_ne : (Icc (ε' / 2) 1).Nonempty := ⟨1, by linarith, le_rfl⟩
  have hF_cont_I : ContinuousOn F (Icc (ε' / 2) 1) := fun t ht =>
    (hF_deriv t (hI_sub ht)).continuousAt.continuousWithinAt
  have hF'_cont_I : ContinuousOn F' (Icc (ε' / 2) 1) := hF'_cont.mono hI_sub
  have hM_cont_I : ContinuousOn M (Icc (ε' / 2) 1) := hM_cont.mono hI_sub
  -- Minimum of F' and maximum of M on [ε'/2, 1]
  obtain ⟨t_fmin, ht_fmin, hfmin⟩ := hI_comp.exists_isMinOn hI_ne hF'_cont_I
  obtain ⟨t_fmax, ht_fmax, hfmax⟩ := hI_comp.exists_isMaxOn hI_ne hF'_cont_I
  obtain ⟨t_mmax, ht_mmax, hmmax⟩ := hI_comp.exists_isMaxOn hI_ne hM_cont_I
  set fmin : ℝ := F' t_fmin
  set fmax : ℝ := F' t_fmax
  set mmax : ℝ := M t_mmax
  have hfmin_pos : 0 < fmin := hF'_pos t_fmin (hI_sub ht_fmin)
  have hmmax_lt1 : mmax < 1 := (hM_mem t_mmax (hI_sub ht_mmax)).2
  have h1m_pos : 0 < 1 - mmax := sub_pos.2 hmmax_lt1
  -- Choose δ > 0 so that for all t ∈ [ε', 1]:
  -- 2 * δ < F'(t) and exp(-δ) * ((1 - exp(-F'(t) + 2δ)) / (1 - exp(-F'(t))))^(1/(1-M(t))) ≥ exp(-ε + δ)
  -- Wait: for t ∈ [ε'/2, 1], (1 - exp(-F'(t) + 2δ)) / (1 - exp(-F'(t))) ≥ 1 - (exp(2δ) - 1) / (exp(fmin) - 1)!
  have hexp_fmin : 1 < Real.exp fmin := Real.one_lt_exp_iff.2 hfmin_pos
  have hcont_g : ContinuousAt (fun d : ℝ =>
      Real.exp (-d) * (1 - (Real.exp (2 * d) - 1) / (Real.exp fmin - 1)) ^ (1 / (1 - mmax)) -
      Real.exp (-ε + d)) 0 := by
    have h1 : ContinuousAt (fun d : ℝ => 1 - (Real.exp (2 * d) - 1) / (Real.exp fmin - 1)) 0 :=
      continuousAt_const.sub (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.sub
        continuousAt_const).div_const _)
    have h10 : 1 - (Real.exp (2 * (0 : ℝ)) - 1) / (Real.exp fmin - 1) ≠ 0 := by simp
    have h2 : ContinuousAt (fun d : ℝ =>
        (1 - (Real.exp (2 * d) - 1) / (Real.exp fmin - 1)) ^ (1 / (1 - mmax))) 0 :=
      h1.rpow_const (Or.inl h10)
    have h3 : ContinuousAt (fun d : ℝ => Real.exp (-d)) 0 :=
      Real.continuous_exp.continuousAt.comp continuousAt_neg
    have h4 : ContinuousAt (fun d : ℝ => Real.exp (-ε + d)) 0 :=
      Real.continuous_exp.continuousAt.comp (continuousAt_const.add continuousAt_id)
    exact (h3.mul h2).sub h4
  have hg0 : 0 < Real.exp (-(0 : ℝ)) * (1 - (Real.exp (2 * (0 : ℝ)) - 1) / (Real.exp fmin - 1)) ^
      (1 / (1 - mmax)) - Real.exp (-ε + (0 : ℝ)) := by
    simp only [neg_zero, Real.exp_zero, mul_zero, sub_self, zero_div, sub_zero, Real.one_rpow,
      one_mul, add_zero, sub_pos]
    exact Real.exp_lt_one_iff.2 (by linarith)
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuousAt_iff.1 hcont_g _ hg0
  let δ : ℝ := min (min (δ₀ / 2) (fmin / 4)) (ε / 4)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_lt_δ₀ : δ < δ₀ := by
    have : δ ≤ δ₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have h2δ_lt_fmin : 2 * δ < fmin := by
    have : δ ≤ fmin / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hδ_ratio_lb : Real.exp (-ε + δ) ≤
      Real.exp (-δ) * (1 - (Real.exp (2 * δ) - 1) / (Real.exp fmin - 1)) ^ (1 / (1 - mmax)) := by
    have hdist : dist δ 0 < δ₀ := by rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]; exact hδ_lt_δ₀
    have h := hδ₀ hdist
    rw [Real.dist_eq, abs_lt] at h
    have h0val : Real.exp (-(0 : ℝ)) * (1 - (Real.exp (2 * (0 : ℝ)) - 1) / (Real.exp fmin - 1)) ^
        (1 / (1 - mmax)) - Real.exp (-ε + (0 : ℝ)) = 1 - Real.exp (-ε) := by simp
    rw [h0val] at h
    linarith
  have hfrac_pos : 0 < 1 - (Real.exp (2 * δ) - 1) / (Real.exp fmin - 1) := by
    rw [sub_pos, div_lt_one (sub_pos.2 hexp_fmin)]
    have : Real.exp (2 * δ) < Real.exp fmin := Real.exp_lt_exp.2 h2δ_lt_fmin
    linarith
  have hδ_ineq : ∀ t ∈ Icc (ε' / 2) 1,
      2 * δ < F' t ∧
      Real.exp (-ε + δ) ≤
        Real.exp (-δ) * ((1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t))) ^ (1 / (1 - M t)) := by
    intro t ht
    have hFt_ge : fmin ≤ F' t := hfmin ht
    have hMt_le : M t ≤ mmax := hmmax ht
    have hMt_lt1 : M t < 1 := (hM_mem t (hI_sub ht)).2
    have hFt_pos : 0 < F' t := hF'_pos t (hI_sub ht)
    refine ⟨by linarith, ?_⟩
    have hratio1 : 1 - (Real.exp (2 * δ) - 1) / (Real.exp fmin - 1) ≤
        (1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t)) := by
      have hden_pos : 0 < 1 - Real.exp (-F' t) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
      have heq : (1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t)) =
          1 - (Real.exp (2 * δ) - 1) / (Real.exp (F' t) - 1) := by
        have hposF : 0 < Real.exp (F' t) - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 hFt_pos)
        have hneg : Real.exp (-F' t) = (Real.exp (F' t))⁻¹ := Real.exp_neg (F' t)
        have hadd : Real.exp (-F' t + 2 * δ) = (Real.exp (F' t))⁻¹ * Real.exp (2 * δ) := by
          rw [Real.exp_add, Real.exp_neg]
        rw [hneg, hadd]
        field_simp [hden_pos.ne', hposF.ne', (Real.exp_pos (F' t)).ne']
        ring
      rw [heq]
      apply sub_le_sub_left
      exact div_le_div_of_nonneg_left (by linarith [Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * δ)])
        (sub_pos.2 hexp_fmin) (by linarith [Real.exp_le_exp.2 hFt_ge])
    have hratio_le1 : (1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t)) ≤ 1 := by
      rw [div_le_one (sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith)))]
      linarith [Real.exp_le_exp.2 (show -F' t ≤ -F' t + 2 * δ by linarith)]
    have hexp_le : 1 / (1 - M t) ≤ 1 / (1 - mmax) :=
      one_div_le_one_div_of_le h1m_pos (by linarith)
    have hpow1 : (1 - (Real.exp (2 * δ) - 1) / (Real.exp fmin - 1)) ^ (1 / (1 - mmax)) ≤
        ((1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t))) ^ (1 / (1 - mmax)) :=
      Real.rpow_le_rpow hfrac_pos.le hratio1 (by positivity)
    have hpow2 : ((1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t))) ^ (1 / (1 - mmax)) ≤
        ((1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t))) ^ (1 / (1 - M t)) :=
      Real.rpow_le_rpow_of_exponent_ge (hfrac_pos.trans_le hratio1) hratio_le1 hexp_le
    exact hδ_ratio_lb.trans (mul_le_mul_of_nonneg_left (hpow1.trans hpow2) (Real.exp_pos _).le)
  -- Uniform continuity of F and F' on [ε'/2, 1]
  have hucF := hI_comp.uniformContinuousOn_of_continuous hF_cont_I
  have hucF' := hI_comp.uniformContinuousOn_of_continuous hF'_cont_I
  rw [Metric.uniformContinuousOn_iff] at hucF hucF'
  obtain ⟨η₁, hη₁_pos, hη₁⟩ := hucF (ε / 2) (half_pos hε)
  obtain ⟨η₂, hη₂_pos, hη₂⟩ := hucF' (δ / 2) (half_pos hδ_pos)
  let ε'' : ℝ := min (min (η₁ / 2) (η₂ / 2)) (ε' / 4)
  have hε''_pos : 0 < ε'' := by dsimp [ε'']; positivity
  -- Build finite grid Λ = {1 - i * ε'' | i ∈ range (M_grid + 1)} covering [ε', 1]
  let M_grid : ℕ := ⌈(1 - ε') / ε''⌉₊
  -- For each i ≤ M_grid, define t_i = max (ε'/2) (1 - i * ε'') ∈ [ε'/2, 1]
  let gridPt (i : ℕ) : ℝ := max (ε' / 2) (1 - (i : ℝ) * ε'')
  have hgrid_mem : ∀ i : ℕ, gridPt i ∈ Icc (ε' / 2) 1 := fun i => by
    refine ⟨le_max_left _ _, max_le (by linarith) ?_⟩
    have : 0 ≤ (i : ℝ) * ε'' := by positivity
    linarith
  -- Apply book_cor at each grid point i ∈ Fin (M_grid + 1)
  have hgrid_L : ∀ i : Fin (M_grid + 1),
      ∃ L_i : ℕ, ∀ (N k l : ℕ), 1 ≤ k → L_i ≤ l →
        let t := gridPt i.1
        let p_t := 1 - Real.exp (-F' t + 2 * δ)
        let μ_t := M t
        let x_t := Real.exp (-δ) * p_t ^ (1 / (1 - μ_t)) * (1 - μ_t)
        ∀ y_t : ℝ, (y_t = Real.exp (-δ) * (Classical.choose (hcond t (hI_sub (hgrid_mem i.1))))) →
        (x_t ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ_t * y_t) ^ l)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) →
        ∀ G : SimpleGraph (Fin N), [DecidableRel G.Adj] →
        p_t * ((N : ℝ) * ((N : ℝ) - 1)) ≤ (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ) →
        (∃ s : Finset (Fin N), G.IsNClique k s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique l s) := by
    intro i
    set t := gridPt i.1
    have htI : t ∈ Icc (ε' / 2) 1 := hgrid_mem i.1
    have ht01 : t ∈ Ioc (0 : ℝ) 1 := hI_sub htI
    set Yt := Classical.choose (hcond t ht01)
    have hYt := Classical.choose_spec (hcond t ht01)
    rcases hYt with ⟨hYt0, hYt1, hInR_t, _⟩
    set p_t := 1 - Real.exp (-F' t + 2 * δ)
    set μ_t := M t
    set Xt := (1 - Real.exp (-F' t)) ^ (1 / (1 - μ_t)) * (1 - μ_t)
    set x_t := Real.exp (-δ) * p_t ^ (1 / (1 - μ_t)) * (1 - μ_t)
    set y_t := Real.exp (-δ) * Yt
    have h2δ : 2 * δ < F' t := (hδ_ineq t htI).1
    have hp_t0 : 0 < p_t := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
    have hp_t1 : p_t < 1 := sub_lt_self 1 (Real.exp_pos _)
    have hμ_t0 : 0 < μ_t := (hM_mem t ht01).1
    have hμ_t1 : μ_t < 1 := (hM_mem t ht01).2
    have hx_t0 : 0 < x_t := by positivity
    have hx_t_lt : x_t < p_t ^ (1 / (1 - μ_t)) * (1 - μ_t) := by
      have he1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      have hpos : 0 < p_t ^ (1 / (1 - μ_t)) * (1 - μ_t) := by positivity
      dsimp [x_t]; nlinarith
    have hx_t_lt_Xt : x_t < Xt := by
      have hp_lt : p_t < 1 - Real.exp (-F' t) := by
        dsimp [p_t]; linarith [Real.exp_lt_exp.2 (show -F' t < -F' t + 2 * δ by linarith)]
      have hpow : p_t ^ (1 / (1 - μ_t)) ≤ (1 - Real.exp (-F' t)) ^ (1 / (1 - μ_t)) :=
        Real.rpow_le_rpow hp_t0.le hp_lt.le (by positivity)
      have h1 : p_t ^ (1 / (1 - μ_t)) * (1 - μ_t) ≤ Xt :=
        mul_le_mul_of_nonneg_right hpow (sub_pos.2 hμ_t1).le
      exact hx_t_lt.trans_le h1
    have hx_t1 : x_t < 1 := hx_t_lt_Xt.trans hInR_t.2.1
    have hy_t0 : 0 < y_t := mul_pos (Real.exp_pos _) hYt0
    have hy_t_lt : y_t < Yt := by
      have he1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      dsimp [y_t]; nlinarith
    have hy_t1 : y_t < 1 := hy_t_lt.trans hYt1
    obtain ⟨L_i, hL_i⟩ := book_cor hμ_t0 hμ_t1 hx_t0 hx_t1 hy_t0 hy_t1 hp_t0 hp_t1 hx_t_lt
      ⟨Xt, Yt, hx_t_lt_Xt, hy_t_lt, hInR_t⟩
    refine ⟨L_i, fun N k l hk hl y' hy' hN G _ hdens => ?_⟩
    subst hy'
    exact hL_i N k l hk hl hN G hdens
  -- Take L = max over all i ∈ Fin (M_grid + 1) of L_i
  choose L_fn hL_fn using hgrid_L
  let L : ℕ := (Finset.univ.image L_fn).max' (Finset.image_nonempty.2 Finset.univ_nonempty)
  -- Claim c:gen: for k ≥ l ≥ max L (ε' * k), any graph on N ≥ exp((F(l/k) + ε) k) with red density ≥ 1 - exp(-F'(l/k) + δ)
  -- has a red K_k or a blue K_l.
  have hclaim : ∀ (N k l : ℕ), 1 ≤ k → L ≤ l → l ≤ k → ε' * (k : ℝ) ≤ (l : ℝ) →
      Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) ≤ (N : ℝ) →
      ∀ G : SimpleGraph (Fin N), [DecidableRel G.Adj] →
      (1 - Real.exp (-F' ((l : ℝ) / (k : ℝ)) + δ)) * ((N : ℝ) * ((N : ℝ) - 1)) ≤
        (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ) →
      (∃ s : Finset (Fin N), G.IsNClique k s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique l s) := by
    intro N k l hk hlL hlk hlε' hN G _ hdens
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    set lam : ℝ := (l : ℝ) / (k : ℝ)
    have hlam_ge : ε' ≤ lam := (le_div_iff₀ hk_pos).2 hlε'
    have hlam_le1 : lam ≤ 1 := (div_le_one hk_pos).2 (by exact_mod_cast hlk)
    have hlam_I : lam ∈ Icc (ε' / 2) 1 := ⟨by linarith, hlam_le1⟩
    -- Pick i = ⌊(1 - lam) / ε''⌋₊; then lam ≤ 1 - i * ε'' ≤ lam + ε''
    let i_nat : ℕ := ⌊(1 - lam) / ε''⌋₊
    have hi_le_M : i_nat ≤ M_grid := by
      have h1 : (1 - lam) / ε'' ≤ (1 - ε') / ε'' :=
        div_le_div_of_nonneg_right (by linarith) hε''_pos.le
      exact (Nat.floor_le_ceil _).trans (Nat.ceil_mono h1)
    let i : Fin (M_grid + 1) := ⟨i_nat, Nat.lt_succ_of_le hi_le_M⟩
    set t : ℝ := gridPt i.1
    have ht_eq : t = 1 - (i_nat : ℝ) * ε'' := by
      dsimp [t, gridPt, i]
      apply max_eq_right
      have hfl : (i_nat : ℝ) ≤ (1 - lam) / ε'' := Nat.floor_le (div_nonneg (by linarith) hε''_pos.le)
      have hmul : (i_nat : ℝ) * ε'' ≤ 1 - lam := (le_div_iff₀ hε''_pos).1 hfl
      linarith
    have hlam_le_t : lam ≤ t := by
      rw [ht_eq]
      have hfl : (i_nat : ℝ) ≤ (1 - lam) / ε'' := Nat.floor_le (div_nonneg (by linarith) hε''_pos.le)
      have hmul : (i_nat : ℝ) * ε'' ≤ 1 - lam := (le_div_iff₀ hε''_pos).1 hfl
      linarith
    have ht_le_lam : t ≤ lam + ε'' := by
      rw [ht_eq]
      have hfl : (1 - lam) / ε'' < (i_nat : ℝ) + 1 := Nat.lt_floor_add_one _
      have hmul : 1 - lam < ((i_nat : ℝ) + 1) * ε'' := (div_lt_iff₀ hε''_pos).1 hfl
      linarith
    have hdist_lt1 : dist lam t < η₁ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      have : ε'' ≤ η₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    have hdist_lt2 : dist lam t < η₂ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      have : ε'' ≤ η₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    have hF_close : |F lam - F t| < ε / 2 := by
      simpa [Real.dist_eq] using hη₁ lam hlam_I t (hgrid_mem i.1) hdist_lt1
    have hF'_close : |F' lam - F' t| < δ / 2 := by
      simpa [Real.dist_eq] using hη₂ lam hlam_I t (hgrid_mem i.1) hdist_lt2
    -- Density bound: 1 - exp(-F'(t) + 2δ) ≤ 1 - exp(-F'(lam) + δ)
    have hdens_t : (1 - Real.exp (-F' t + 2 * δ)) * ((N : ℝ) * ((N : ℝ) - 1)) ≤
        (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ) := by
      have hle_p : 1 - Real.exp (-F' t + 2 * δ) ≤ 1 - Real.exp (-F' lam + δ) := by
        have h1 : -F' lam + δ ≤ -F' t + 2 * δ := by
          rw [abs_lt] at hF'_close; linarith
        linarith [Real.exp_le_exp.2 h1]
      have hN1_nn : (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) := by
        have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by
          have : (0 : ℝ) ≤ (F lam + ε) * (k : ℝ) := by
            have := hF_pos lam (hI_sub hlam_I); positivity
          exact (Real.one_le_exp this).trans hN
        nlinarith
      exact (mul_le_mul_of_nonneg_right hle_p hN1_nn).trans hdens
    -- Size bound for book_cor at i
    set Yt := Classical.choose (hcond t (hI_sub (hgrid_mem i.1)))
    have hYt := Classical.choose_spec (hcond t (hI_sub (hgrid_mem i.1)))
    rcases hYt with ⟨hYt0, hYt1, hInR_t, hPhi_t⟩
    set p_t := 1 - Real.exp (-F' t + 2 * δ)
    set μ_t := M t
    set Xt := (1 - Real.exp (-F' t)) ^ (1 / (1 - μ_t)) * (1 - μ_t)
    set x_t := Real.exp (-δ) * p_t ^ (1 / (1 - μ_t)) * (1 - μ_t)
    set y_t := Real.exp (-δ) * Yt
    have h2δ : 2 * δ < F' t := (hδ_ineq t (hgrid_mem i.1)).1
    have hp_t0 : 0 < p_t := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
    have hμ_t0 : 0 < μ_t := (hM_mem t (hI_sub (hgrid_mem i.1))).1
    have hμ_t1 : μ_t < 1 := (hM_mem t (hI_sub (hgrid_mem i.1))).2
    have hXt0 : 0 < Xt := by
      have : 0 < 1 - Real.exp (-F' t) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
      positivity
    have hx_t0 : 0 < x_t := by positivity
    have hy_t0 : 0 < y_t := by positivity
    have hx_t_ge : Real.exp (-ε + δ) * Xt ≤ x_t := by
      have hr := (hδ_ineq t (hgrid_mem i.1)).2
      have h1 : x_t = Real.exp (-δ) * ((1 - Real.exp (-F' t + 2 * δ)) / (1 - Real.exp (-F' t))) ^
          (1 / (1 - μ_t)) * Xt := by
        dsimp [x_t, Xt]
        have hposF : 0 < 1 - Real.exp (-F' t) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
        rw [show 1 - Real.exp (-F' t + 2 * δ) = p_t from rfl, Real.div_rpow hp_t0.le hposF.le]
        field_simp [(Real.rpow_pos_of_pos hposF _).ne']
      rw [h1]
      exact mul_le_mul_of_nonneg_right hr hXt0.le
    have hN_req : (x_t ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ_t * y_t) ^ l)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) := by
      -- Compare logs of LHS and exp((F(lam) + ε) k)
      have hlhs_eq : (x_t ^ k)⁻¹ ^ ((1 : ℝ) / 2) * ((μ_t * y_t) ^ l)⁻¹ ^ ((1 : ℝ) / 2) =
          Real.exp (-(1 / 2) * ((k : ℝ) * Real.log x_t + (l : ℝ) * Real.log μ_t + (l : ℝ) * Real.log y_t)) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
        congr 1
        rw [Real.log_inv, Real.log_inv, Real.log_pow, Real.log_pow, Real.log_mul hμ_t0.ne' hy_t0.ne']
        ring
      rw [hlhs_eq]
      refine (Real.exp_le_exp.2 ?_).trans hN
      have hlog_xt : -ε + δ + Real.log Xt ≤ Real.log x_t := by
        have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hXt0) hx_t_ge
        rw [Real.log_mul (Real.exp_pos _).ne' hXt0.ne', Real.log_exp] at h1
        exact h1
      have hlog_yt : Real.log y_t = -δ + Real.log Yt := by
        dsimp [y_t]; rw [Real.log_mul (Real.exp_pos _).ne' hYt0.ne', Real.log_exp]
      have hlog_neg : Real.log μ_t + Real.log Yt < 0 :=
        add_neg (Real.log_neg hμ_t0 hμ_t1) (Real.log_neg hYt0 hYt1)
      have hl_le_tk : (l : ℝ) ≤ t * (k : ℝ) := (div_le_iff₀ hk_pos).1 hlam_le_t
      have hterm_l : t * (k : ℝ) * (Real.log μ_t + Real.log Yt) ≤
          (l : ℝ) * (Real.log μ_t + Real.log Yt) :=
        mul_le_mul_of_nonpos_right hl_le_tk hlog_neg.le
      have hl_le_k : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
      have hF_lam_ge : F t + ε / 2 ≤ F lam + ε := by
        rw [abs_lt] at hF_close; linarith
      -- Combine:
      -- -(1/2) * (k log x_t + l log μ_t + l log y_t)
      -- ≤ -(1/2) * (k (-ε + δ + log Xt) + l (-δ) + t k (log μ_t + log Yt))
      -- = -(1/2) * (log Xt + t log μ_t + t log Yt) * k + (ε/2) k - (δ/2) (k - l)
      -- ≤ F(t) k + (ε/2) k ≤ (F(lam) + ε) k
      have hstep1 : -(1 / 2) * ((k : ℝ) * Real.log x_t + (l : ℝ) * Real.log μ_t + (l : ℝ) * Real.log y_t) ≤
          -(Real.log Xt + t * Real.log μ_t + t * Real.log Yt) / 2 * (k : ℝ) +
          (ε / 2) * (k : ℝ) - (δ / 2) * ((k : ℝ) - (l : ℝ)) := by
        rw [hlog_yt]
        nlinarith only [hlog_xt, hterm_l, hk_pos]
      have hstep2 : -(Real.log Xt + t * Real.log μ_t + t * Real.log Yt) / 2 * (k : ℝ) ≤ F t * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hPhi_t.le hk_pos.le
      have hstep3 : 0 ≤ (δ / 2) * ((k : ℝ) - (l : ℝ)) :=
        mul_nonneg (by linarith only [hδ_pos]) (by linarith only [hl_le_k])
      nlinarith only [hstep1, hstep2, hstep3, hF_lam_ge, hk_pos]
    have hLi_le : L_fn i ≤ l := (Finset.le_max' _ _ (Finset.mem_image_of_mem L_fn (Finset.mem_univ i))).trans hlL
    exact hL_fn i N k l hk hLi_le y_t rfl hN_req G hdens_t
  -- Now prove R(k, l) ≤ exp((F(l/k) + ε) k) for sufficiently large k by induction on l!
  -- Choose K large enough so that:
  -- (1) ε' * K ≥ L + 2 (so l > ε' * k implies l ≥ L and (l-1)/k ≥ ε'/2)
  -- (2) 1 / K < η₂ (so |F'(l/k) - F'(c)| ≤ δ/2 for c ∈ [(l-1)/k, l/k])
  -- (3) exp(ε * K) ≥ exp(fmax) / (exp(δ/2) - 1) + 2 (so exp(-F'(l/k) + δ) * N - 1 ≥ exp(-F'(l/k) + δ/2) * N)
  have heδ2 : 0 < Real.exp (δ / 2) - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 (half_pos hδ_pos))
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt (((L : ℝ) + 2) / ε')
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (1 / η₂)
  obtain ⟨K₃, hK₃⟩ := exists_nat_gt
    (Real.log ((Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1) / ε)
  let K : ℕ := max (max K₁ K₂) (max K₃ 4)
  refine ⟨K, fun k l hkK hl1 hlk => ?_⟩
  have hk_pos : (0 : ℝ) < k := by
    have : 4 ≤ k := ((le_max_right K₃ 4).trans (le_max_right _ _)).trans hkK
    exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ k := by
    have : 4 ≤ k := ((le_max_right K₃ 4).trans (le_max_right _ _)).trans hkK
    omega
  -- Induct on l (with k fixed)
  induction l with
  | zero => omega
  | succ l' ih =>
    by_cases hsmall_l : ((l' + 1 : ℕ) : ℝ) ≤ ε' * (k : ℝ)
    · have h1 := hsmall k (l' + 1) hk1 (by omega) hsmall_l
      have hFnn : 0 ≤ F (((l' + 1 : ℕ) : ℝ) / (k : ℝ)) :=
        hF_pos _ ⟨div_pos (by positivity) hk_pos, (div_le_one hk_pos).2 (by exact_mod_cast hlk)⟩
      have h2 : Real.exp (ε * (k : ℝ)) ≤ Real.exp ((F (((l' + 1 : ℕ) : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) :=
        Real.exp_le_exp.2 (by nlinarith)
      linarith
    · have hl_gt : ε' * (k : ℝ) < ((l' + 1 : ℕ) : ℝ) := lt_of_not_ge hsmall_l
      have hK1_le : K₁ ≤ k := ((le_max_left K₁ K₂).trans (le_max_left _ _)).trans hkK
      have hK2_le : K₂ ≤ k := ((le_max_right K₁ K₂).trans (le_max_left _ _)).trans hkK
      have hK3_le : K₃ ≤ k := ((le_max_left K₃ 4).trans (le_max_right _ _)).trans hkK
      have hlL : L ≤ l' + 1 := by
        have hlt : ((L : ℝ) + 2) / ε' < (k : ℝ) := hK₁.trans_le (by exact_mod_cast hK1_le)
        have hmul : (L : ℝ) + 2 < ε' * (k : ℝ) := by
          have := (div_lt_iff₀ hε'0).1 hlt; linarith
        have : (L : ℝ) < ((l' + 1 : ℕ) : ℝ) := by linarith
        exact_mod_cast this.le
      have hl'_pos : 1 ≤ l' := by
        have hlt : ((L : ℝ) + 2) / ε' < (k : ℝ) := hK₁.trans_le (by exact_mod_cast hK1_le)
        have hmul : (L : ℝ) + 2 < ε' * (k : ℝ) := by
          have := (div_lt_iff₀ hε'0).1 hlt; linarith
        have : (2 : ℝ) < ((l' + 1 : ℕ) : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
        have : 2 ≤ l' + 1 := by exact_mod_cast this.le
        omega
      -- Let N = ⌈exp((F((l'+1)/k) + ε) k)⌉₊; show HasRamsey k (l'+1) N
      set lam : ℝ := ((l' + 1 : ℕ) : ℝ) / (k : ℝ)
      set lam' : ℝ := (l' : ℝ) / (k : ℝ)
      let N : ℕ := ⌈Real.exp ((F lam + ε) * (k : ℝ))⌉₊
      have hN_ge : Real.exp ((F lam + ε) * (k : ℝ)) ≤ (N : ℝ) := Nat.le_ceil _
      have hN_lt : (N : ℝ) < Real.exp ((F lam + ε) * (k : ℝ)) + 1 :=
        Nat.ceil_lt_add_one (Real.exp_pos _).le
      have hmain_hasRamsey : HasRamsey k (l' + 1) N := by
        intro G
        classical
        set p_lam : ℝ := 1 - Real.exp (-F' lam + δ)
        by_cases hdens : p_lam * ((N : ℝ) * ((N : ℝ) - 1)) ≤
            (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ)
        · exact hclaim N k (l' + 1) hk1 hlL hlk hl_gt.le hN_ge G hdens
        · -- Red edge density < p_lam, so blue edge density > exp(-F' lam + δ)
          have hdens_lt : (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card : ℝ) <
              p_lam * ((N : ℝ) * ((N : ℝ) - 1)) := lt_of_not_ge hdens
          have hlam_ge_ε' : ε' ≤ lam := (le_div_iff₀ hk_pos).2 hl_gt.le
          have hlam_le1 : lam ≤ 1 := (div_le_one hk_pos).2 (by exact_mod_cast hlk)
          have hlam_I : lam ∈ Icc (ε' / 2) 1 := ⟨by linarith, hlam_le1⟩
          have hlam'_ge : ε' / 2 ≤ lam' := by
            have hlt : ((L : ℝ) + 2) / ε' < (k : ℝ) := hK₁.trans_le (by exact_mod_cast hK1_le)
            have hmul : (L : ℝ) + 2 < ε' * (k : ℝ) := by
              have := (div_lt_iff₀ hε'0).1 hlt; linarith
            have h2k : (2 : ℝ) / (k : ℝ) < ε' := by
              rw [div_lt_iff₀ hk_pos]; linarith [Nat.cast_nonneg (α := ℝ) L]
            have hdiff : lam - lam' = 1 / (k : ℝ) := by
              dsimp [lam, lam']; push_cast; ring
            have h1k : 1 / (k : ℝ) < ε' / 2 := by
              have : (2 : ℝ) / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
              linarith
            linarith
          have hlam'_lt : lam' < lam := by
            dsimp [lam, lam']
            exact div_lt_div_of_pos_right (by push_cast; linarith) hk_pos
          have hlam'_I : lam' ∈ Icc (ε' / 2) 1 := ⟨hlam'_ge, hlam'_lt.le.trans hlam_le1⟩
          have hN_ge_thresh : (Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1 ≤ (N : ℝ) := by
            have hK3_lt : Real.log ((Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1) / ε < (k : ℝ) :=
              hK₃.trans_le (by exact_mod_cast hK3_le)
            have hlog_lt : Real.log ((Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1) < ε * (k : ℝ) := by
              have := (div_lt_iff₀ hε).1 hK3_lt; linarith
            have hFnn : 0 ≤ F lam := hF_pos lam (hI_sub hlam_I)
            have h1 : (Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1 ≤ Real.exp (ε * (k : ℝ)) := by
              have hpos_arg : 0 < (Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) + 1 := by positivity
              calc _ = Real.exp (Real.log _) := (Real.exp_log hpos_arg).symm
                _ ≤ Real.exp (ε * (k : ℝ)) := Real.exp_le_exp.2 hlog_lt.le
            have h2 : Real.exp (ε * (k : ℝ)) ≤ Real.exp ((F lam + ε) * (k : ℝ)) :=
              Real.exp_le_exp.2 (by nlinarith)
            exact h1.trans (h2.trans hN_ge)
          have hN_pos : 0 < N := by
            have : (1 : ℝ) < (N : ℝ) := by
              have : 0 < (Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) := by positivity
              linarith
            exact_mod_cast (show (0 : ℝ) < (N : ℝ) by linarith)
          -- Sum of blue degrees + red degrees = N * (N - 1)
          have hdeg_sum : ∀ u : Fin N,
              (Finset.univ.filter (Gᶜ.Adj u)).card + (Finset.univ.filter (G.Adj u)).card = N - 1 := by
            intro u
            have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase u) (p := G.Adj u)
            have herase : (Finset.univ.erase u).card = N - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
            have hf1 : (Finset.univ.erase u).filter (G.Adj u) = Finset.univ.filter (G.Adj u) := by
              ext v; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
              exact ⟨fun h => h.2, fun h => ⟨(G.ne_of_adj h).symm, h⟩⟩
            have hf2 : (Finset.univ.erase u).filter (fun v => ¬ G.Adj u v) = Finset.univ.filter (Gᶜ.Adj u) := by
              ext v; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, SimpleGraph.compl_adj,
                and_true, true_and, ne_comm]
            rw [hf1, hf2, herase] at h1
            omega
          have hblue_sum_nat : (∑ u : Fin N, (Finset.univ.filter (Gᶜ.Adj u)).card) +
              (∑ u : Fin N, (Finset.univ.filter (G.Adj u)).card) = N * (N - 1) := by
            rw [← Finset.sum_add_distrib]
            calc ∑ u : Fin N, ((Finset.univ.filter (Gᶜ.Adj u)).card + (Finset.univ.filter (G.Adj u)).card)
                = ∑ _u : Fin N, (N - 1) := Finset.sum_congr rfl fun u _ => hdeg_sum u
              _ = N * (N - 1) := by simp
          have hblue_sum : Real.exp (-F' lam + δ) * ((N : ℝ) * ((N : ℝ) - 1)) ≤
              (∑ u : Fin N, ((Finset.univ.filter (Gᶜ.Adj u)).card : ℝ)) := by
            have hcast : (∑ u : Fin N, ((Finset.univ.filter (Gᶜ.Adj u)).card : ℝ)) +
                (∑ u : Fin N, ((Finset.univ.filter (G.Adj u)).card : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) := by
              have h := congr_arg (Nat.cast (R := ℝ)) hblue_sum_nat
              push_cast [Nat.cast_sub (show 1 ≤ N by omega)] at h
              exact h
            dsimp [p_lam] at hdens_lt
            nlinarith
          -- Pick vertex v with maximum blue degree ≥ exp(-F' lam + δ) * (N - 1)
          have huniv_ne : (Finset.univ : Finset (Fin N)).Nonempty :=
            Finset.card_pos.1 (by simp [hN_pos])
          obtain ⟨v, _, hvmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N))
            (fun u => (Finset.univ.filter (Gᶜ.Adj u)).card) huniv_ne
          set U : Finset (Fin N) := Finset.univ.filter (Gᶜ.Adj v)
          have hU_card : Real.exp (-F' lam + δ) * ((N : ℝ) - 1) ≤ (U.card : ℝ) := by
            have hsum_ub : (∑ u : Fin N, (Finset.univ.filter (Gᶜ.Adj u)).card : ℝ) ≤ (N : ℝ) * (U.card : ℝ) := by
              have hnat : ∑ u : Fin N, (Finset.univ.filter (Gᶜ.Adj u)).card ≤ N * U.card := by
                calc ∑ u : Fin N, (Finset.univ.filter (Gᶜ.Adj u)).card
                    ≤ ∑ _u : Fin N, U.card := Finset.sum_le_sum fun u _ => hvmax u (Finset.mem_univ u)
                  _ = N * U.card := by simp
              exact_mod_cast hnat
            have hN_pos_r : (0 : ℝ) < N := by exact_mod_cast hN_pos
            nlinarith
          -- Apply MVT to F on [lam', lam] to relate F lam' to F lam - F' lam / k
          have hF_diff : F' lam - δ / 2 ≤ (F lam - F lam') * (k : ℝ) := by
            have hcont_sub : ContinuousOn F (Icc lam' lam) :=
              hF_cont_I.mono (Icc_subset_Icc hlam'_ge hlam_le1)
            have hderiv_sub : ∀ c ∈ Ioo lam' lam, HasDerivAt F (F' c) c := fun c hc =>
              hF_deriv c (hI_sub ⟨hlam'_ge.trans hc.1.le, hc.2.le.trans hlam_le1⟩)
            obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope F F' hlam'_lt hcont_sub hderiv_sub
            have hc_I : c ∈ Icc (ε' / 2) 1 := ⟨hlam'_ge.trans hc_mem.1.le, hc_mem.2.le.trans hlam_le1⟩
            have hdist_c : dist c lam < η₂ := by
              rw [Real.dist_eq, abs_of_neg (sub_neg.2 hc_mem.2)]
              have h1 : lam - c < lam - lam' := by linarith [hc_mem.1]
              have h2 : lam - lam' = 1 / (k : ℝ) := by dsimp [lam, lam']; push_cast; ring
              have h3 : 1 / (k : ℝ) < η₂ := by
                have hlt : 1 / η₂ < (k : ℝ) := hK₂.trans_le (by exact_mod_cast hK2_le)
                rw [div_lt_iff₀ hk_pos]
                have := (div_lt_iff₀ hη₂_pos).1 hlt
                linarith
              linarith
            have hF'_close := hη₂ c hc_I lam hlam_I hdist_c
            rw [Real.dist_eq, abs_lt] at hF'_close
            have hdiff_eq : (F lam - F lam') * (k : ℝ) = F' c := by
              have hsub_eq : lam - lam' = 1 / (k : ℝ) := by dsimp [lam, lam']; push_cast; ring
              have hm := (eq_div_iff (sub_pos.2 hlam'_lt).ne').1 hc_eq
              rw [hsub_eq] at hm
              have hm' := congr_arg (· * (k : ℝ)) hm
              have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
              have h1 : F' c * (1 / (k : ℝ)) * (k : ℝ) = F' c := by field_simp [hk_ne]
              linarith
            linarith
          -- Show ramsey k l' ≤ U.card
          have hR_le_U : (ramsey k l' : ℝ) ≤ (U.card : ℝ) := by
            have hih := ih hl'_pos (by omega)
            have hexp_le : Real.exp ((F lam' + ε) * (k : ℝ)) ≤ Real.exp (-F' lam + δ / 2) * (N : ℝ) := by
              calc Real.exp ((F lam' + ε) * (k : ℝ))
                  ≤ Real.exp ((-F' lam + δ / 2) + (F lam + ε) * (k : ℝ)) :=
                    Real.exp_le_exp.2 (by linarith)
                _ = Real.exp (-F' lam + δ / 2) * Real.exp ((F lam + ε) * (k : ℝ)) := Real.exp_add _ _
                _ ≤ Real.exp (-F' lam + δ / 2) * (N : ℝ) :=
                    mul_le_mul_of_nonneg_left hN_ge (Real.exp_pos _).le
            have hmargin : Real.exp (-F' lam + δ / 2) * (N : ℝ) + 1 ≤
                Real.exp (-F' lam + δ) * ((N : ℝ) - 1) := by
              have hFp_le : F' lam ≤ fmax := hfmax hlam_I
              have hexp_split : Real.exp (-F' lam + δ) = Real.exp (-F' lam + δ / 2) * Real.exp (δ / 2) := by
                rw [← Real.exp_add]; congr 1; ring
              have hN_mul : Real.exp (δ / 2) + Real.exp fmax ≤ (Real.exp (δ / 2) - 1) * (N : ℝ) := by
                have h1 : (Real.exp (δ / 2) + Real.exp fmax) / (Real.exp (δ / 2) - 1) ≤ (N : ℝ) := by linarith
                have := (div_le_iff₀ heδ2).1 h1
                linarith
              have h1le : 1 ≤ Real.exp (-F' lam + δ / 2) * Real.exp fmax := by
                rw [← Real.exp_add]
                exact Real.one_le_exp (by linarith)
              rw [hexp_split]
              have hposE : 0 < Real.exp (-F' lam + δ / 2) := Real.exp_pos _
              have hstep : Real.exp (-F' lam + δ / 2) * (Real.exp (δ / 2) + Real.exp fmax) ≤
                  Real.exp (-F' lam + δ / 2) * ((Real.exp (δ / 2) - 1) * (N : ℝ)) :=
                mul_le_mul_of_nonneg_left hN_mul hposE.le
              linarith
            linarith [hih, hexp_le, hmargin, hU_card]
          have hR_le_U_nat : ramsey k l' ≤ U.card := by exact_mod_cast hR_le_U
          rcases hasRamsey_subset (ramsey_spec k l') G U hR_le_U_nat with ⟨s, _, hscl⟩ | ⟨s, hsU, hscl⟩
          · exact Or.inl ⟨s, hscl⟩
          · refine Or.inr ⟨insert v s, ?_⟩
            have hv_notMem : v ∉ s := fun hvs => by
              have hvU := hsU hvs
              have hadj : Gᶜ.Adj v v := (Finset.mem_filter.1 hvU).2
              exact Gᶜ.ne_of_adj hadj rfl
            rw [SimpleGraph.isNClique_iff] at hscl ⊢
            refine ⟨?_, by rw [Finset.card_insert_of_notMem hv_notMem, hscl.2]⟩
            intro a ha b hb hab
            rcases Finset.mem_insert.1 ha with rfl | ha' <;>
            rcases Finset.mem_insert.1 hb with rfl | hb'
            · exact (hab rfl).elim
            · exact (Finset.mem_filter.1 (hsU hb')).2
            · exact (Gᶜ.adj_comm _ _).1 (Finset.mem_filter.1 (hsU ha')).2
            · exact hscl.1 ha' hb' hab
      have hR_le_N : ramsey k (l' + 1) ≤ N := ramsey_le_of_hasRamsey hmain_hasRamsey
      have hR_le_Nr : (ramsey k (l' + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hR_le_N
      exact hR_le_Nr.trans hN_lt.le

/-- Clean version of GNNW Lemma 14 without the trailing `+ 1`. -/
theorem general_ramsey_bound
    (F F' M : ℝ → ℝ)
    (hF_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'_cont : ContinuousOn F' (Ioc (0 : ℝ) 1))
    (hF_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ F t)
    (hF'_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < F' t)
    (hM_cont : ContinuousOn M (Ioc (0 : ℝ) 1))
    (hM_mem : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < M t ∧ M t < 1)
    (hcond : ∀ t ∈ Ioc (0 : ℝ) 1, ∃ y : ℝ, 0 < y ∧ y < 1 ∧
      let X := (1 - Real.exp (-F' t)) ^ (1 / (1 - M t)) * (1 - M t)
      InR X y ∧
      -(Real.log X + t * Real.log (M t) + t * Real.log y) / 2 < F t) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := general_ramsey_bound_aux F F' M hF_pos hF_deriv hF'_cont hF'_pos hM_cont hM_mem hcond
    (ε / 2) (half_pos hε)
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (2 * Real.log 2 / ε)
  refine ⟨max (max K₁ K₂) 1, fun k l hk hl1 hlk => ?_⟩
  have hk1 : K₁ ≤ k := ((le_max_left K₁ K₂).trans (le_max_left _ 1)).trans hk
  have hk2 : K₂ ≤ k := ((le_max_right K₁ K₂).trans (le_max_left _ 1)).trans hk
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast ((le_max_right _ 1).trans hk)
  have h1 := hK₁ k l hk1 hl1 hlk
  have hFnn : 0 ≤ F ((l : ℝ) / (k : ℝ)) :=
    hF_pos _ ⟨div_pos (by exact_mod_cast hl1) hk_pos, (div_le_one hk_pos).2 (by exact_mod_cast hlk)⟩
  have h1_le_exp : (1 : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε / 2) * (k : ℝ)) :=
    Real.one_le_exp (by positivity)
  have h2_le_exp : (2 : ℝ) ≤ Real.exp ((ε / 2) * (k : ℝ)) := by
    have hlt : 2 * Real.log 2 / ε < (k : ℝ) := hK₂.trans_le (by exact_mod_cast hk2)
    have hmul : Real.log 2 < (ε / 2) * (k : ℝ) := by
      have := (div_lt_iff₀ hε).1 hlt; linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((ε / 2) * (k : ℝ)) := Real.exp_le_exp.2 hmul.le
  calc (ramsey k l : ℝ)
      ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε / 2) * (k : ℝ)) + 1 := h1
    _ ≤ 2 * Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε / 2) * (k : ℝ)) := by linarith
    _ ≤ Real.exp ((ε / 2) * (k : ℝ)) * Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε / 2) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right h2_le_exp (Real.exp_pos _).le
    _ = Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- Helper: given any `x, y ∈ (0, 1)` such that `F(s) + log x + s log y ≤ 0` and
`F(s) + s log x + log y ≤ 0` for all `s ∈ (0, 1]`, a Ramsey upper bound with `F` implies `InR x y`. -/
lemma inR_of_ramsey_bound
    (F : ℝ → ℝ)
    (hRam : ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)))
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (h1 : ∀ s ∈ Ioc (0 : ℝ) 1, F s + Real.log x + s * Real.log y ≤ 0)
    (h2 : ∀ s ∈ Ioc (0 : ℝ) 1, F s + s * Real.log x + Real.log y ≤ 0) :
    InR x y := by
  apply inR_of_asymp hx0 hx1 hy0 hy1
  intro ε hε
  obtain ⟨K, hK⟩ := hRam ε hε
  refine ⟨max K 1, fun k l hk hl => ?_⟩
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  have hl1 : 1 ≤ l := (le_max_right K 1).trans hl
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  have hlK : K ≤ l := (le_max_left K 1).trans hl
  by_cases hlk : l ≤ k
  · have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hs_mem : (l : ℝ) / (k : ℝ) ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos (by exact_mod_cast hl1) hk_pos, (div_le_one hk_pos).2 (by exact_mod_cast hlk)⟩
    have hF := h1 ((l : ℝ) / (k : ℝ)) hs_mem
    have hmul : (F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ) ≤
        ε * ((k : ℝ) + (l : ℝ)) - (k : ℝ) * Real.log x - (l : ℝ) * Real.log y := by
      have hmul1 := mul_le_mul_of_nonneg_right hF hk_pos.le
      have hcancel : (l : ℝ) / (k : ℝ) * Real.log y * (k : ℝ) = (l : ℝ) * Real.log y := by
        field_simp [hk_pos.ne']
      have hl_nn : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      nlinarith
    have hR := hK k l hkK hl1 hlk
    calc (ramsey k l : ℝ)
        ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := hR
      _ ≤ Real.exp (ε * ((k : ℝ) + (l : ℝ)) - (k : ℝ) * Real.log x - (l : ℝ) * Real.log y) :=
          Real.exp_le_exp.2 hmul
      _ = (x ^ k)⁻¹ * (y ^ l)⁻¹ * Real.exp (ε * ((k : ℝ) + (l : ℝ))) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add,
              Real.exp_neg, Real.exp_neg, Real.exp_nat_mul, Real.exp_nat_mul,
              Real.exp_log hx0, Real.exp_log hy0]; ring
  · have hkl' : k ≤ l := by omega
    have hl_pos : (0 : ℝ) < l := by exact_mod_cast hl1
    have hs_mem : (k : ℝ) / (l : ℝ) ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos (by exact_mod_cast hk1) hl_pos, (div_le_one hl_pos).2 (by exact_mod_cast hkl')⟩
    have hF := h2 ((k : ℝ) / (l : ℝ)) hs_mem
    have hmul : (F ((k : ℝ) / (l : ℝ)) + ε) * (l : ℝ) ≤
        ε * ((k : ℝ) + (l : ℝ)) - (k : ℝ) * Real.log x - (l : ℝ) * Real.log y := by
      have hmul1 := mul_le_mul_of_nonneg_right hF hl_pos.le
      have hcancel : (k : ℝ) / (l : ℝ) * Real.log x * (l : ℝ) = (k : ℝ) * Real.log x := by
        field_simp [hl_pos.ne']
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hR : (ramsey k l : ℝ) ≤ Real.exp ((F ((k : ℝ) / (l : ℝ)) + ε) * (l : ℝ)) := by
      rw [ramsey_symm]; exact hK l k hlK hk1 hkl'
    calc (ramsey k l : ℝ)
        ≤ Real.exp ((F ((k : ℝ) / (l : ℝ)) + ε) * (l : ℝ)) := hR
      _ ≤ Real.exp (ε * ((k : ℝ) + (l : ℝ)) - (k : ℝ) * Real.log x - (l : ℝ) * Real.log y) :=
          Real.exp_le_exp.2 hmul
      _ = (x ^ k)⁻¹ * (y ^ l)⁻¹ * Real.exp (ε * ((k : ℝ) + (l : ℝ))) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add,
              Real.exp_neg, Real.exp_neg, Real.exp_nat_mul, Real.exp_nat_mul,
              Real.exp_log hx0, Real.exp_log hy0]; ring

/-- Concavity tangent inequality for a differentiable function with antitone derivative on `(0, 1]`. -/
lemma tangent_le_of_antitone_deriv
    (F F' : ℝ → ℝ)
    (hF_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'_anti : AntitoneOn F' (Ioc (0 : ℝ) 1))
    {t s : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (hs : s ∈ Ioc (0 : ℝ) 1) :
    F s ≤ F t + F' t * (s - t) := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hcont : ContinuousOn F (Icc s t) := fun u hu =>
      (hF_deriv u ⟨hs.1.trans_le hu.1, hu.2.trans ht.2⟩).continuousAt.continuousWithinAt
    have hderiv : ∀ u ∈ Ioo s t, HasDerivAt F (F' u) u := fun u hu =>
      hF_deriv u ⟨hs.1.trans hu.1, hu.2.le.trans ht.2⟩
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F F' hst hcont hderiv
    have hFc : F' t ≤ F' c := hF'_anti ⟨hs.1.trans hc.1, hc.2.le.trans ht.2⟩ ht hc.2.le
    have hdiff : F t - F s = F' c * (t - s) := by
      have := (eq_div_iff (sub_pos.2 hst).ne').1 hceq; linarith
    nlinarith
  · linarith
  · have hcont : ContinuousOn F (Icc t s) := fun u hu =>
      (hF_deriv u ⟨ht.1.trans_le hu.1, hu.2.trans hs.2⟩).continuousAt.continuousWithinAt
    have hderiv : ∀ u ∈ Ioo t s, HasDerivAt F (F' u) u := fun u hu =>
      hF_deriv u ⟨ht.1.trans hu.1, hu.2.le.trans hs.2⟩
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F F' hts hcont hderiv
    have hFc : F' c ≤ F' t := hF'_anti ht ⟨ht.1.trans hc.1, hc.2.le.trans hs.2⟩ hc.1.le
    have hdiff : F s - F t = F' c * (s - t) := by
      have := (eq_div_iff (sub_pos.2 hts).ne').1 hceq; linarith
    nlinarith

/-- Frontier membership from a concave Ramsey upper bound function F (GNNW Lemma 15, outer parts):
for every `t ∈ (0, 1]` with `0 < F(t) - t F'(t)` and `F(t) ≤ (1 + t) F'(t)` (i.e., `A(t) ≤ B(t)`),
both `(A(t), B(t))` and `(B(t), A(t))` lie in `InR`, where `A(t) = exp(-F'(t))` and
`B(t) = exp(-(F(t) - t F'(t)))`. -/
theorem frontier_AB
    (F F' : ℝ → ℝ)
    (hF_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'_anti : AntitoneOn F' (Ioc (0 : ℝ) 1))
    (hF'_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < F' t)
    (hRam : ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hB_pos : 0 < F t - t * F' t)
    (hAB : F t ≤ (1 + t) * F' t) :
    InR (Real.exp (-F' t)) (Real.exp (-(F t - t * F' t))) ∧
    InR (Real.exp (-(F t - t * F' t))) (Real.exp (-F' t)) := by
  set A : ℝ := Real.exp (-F' t)
  set B : ℝ := Real.exp (-(F t - t * F' t))
  have hA0 : 0 < A := Real.exp_pos _
  have hA1 : A < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 (hF'_pos t ⟨ht0, ht1⟩))
  have hB0 : 0 < B := Real.exp_pos _
  have hB1 : B < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlogA : Real.log A = -F' t := Real.log_exp _
  have hlogB : Real.log B = -(F t - t * F' t) := Real.log_exp _
  have hBA_s : ∀ s ∈ Ioc (0 : ℝ) 1, F s + Real.log B + s * Real.log A ≤ 0 := by
    intro s hs
    have htan := tangent_le_of_antitone_deriv F F' hF_deriv hF'_anti ⟨ht0, ht1⟩ hs
    rw [hlogA, hlogB]; linarith
  have hAB_s : ∀ s ∈ Ioc (0 : ℝ) 1, F s + Real.log A + s * Real.log B ≤ 0 := by
    intro s hs
    have h1 := hBA_s s hs
    have hlogAB : Real.log A ≤ Real.log B := by rw [hlogA, hlogB]; linarith
    have h1ms : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    nlinarith
  exact ⟨inR_of_ramsey_bound F hRam hA0 hA1 hB0 hB1 hAB_s (fun s hs => by linarith [hBA_s s hs]),
         inR_of_ramsey_bound F hRam hB0 hB1 hA0 hA1 hBA_s (fun s hs => by linarith [hAB_s s hs])⟩

/-- Frontier membership from a concave Ramsey upper bound function F (GNNW Lemma 15, middle part):
for `a = exp(-F'(1)) ≤ x ≤ exp(-(F(1) - F'(1))) = b` and `y = exp(-F(1)) / x`, we have `InR x y`. -/
theorem frontier_mid
    (F F' : ℝ → ℝ)
    (hF_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'_anti : AntitoneOn F' (Ioc (0 : ℝ) 1))
    (_hF'_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < F' t)
    (hRam : ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((F ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)))
    (hB1_pos : 0 < F 1 - F' 1)
    {x : ℝ} (hxa : Real.exp (-F' 1) ≤ x) (hxb : x ≤ Real.exp (-(F 1 - F' 1))) :
    0 < Real.exp (-F 1) / x ∧ Real.exp (-F 1) / x < 1 ∧ InR x (Real.exp (-F 1) / x) := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxa
  have hx1 : x < 1 := hxb.trans_lt (Real.exp_lt_one_iff.2 (by linarith))
  set y : ℝ := Real.exp (-F 1) / x
  have hy0 : 0 < y := div_pos (Real.exp_pos _) hx0
  have hy_le_b : y ≤ Real.exp (-(F 1 - F' 1)) := by
    dsimp [y]
    rw [div_le_iff₀ hx0]
    have hmul : Real.exp (-F 1) = Real.exp (-(F 1 - F' 1)) * Real.exp (-F' 1) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hxa (Real.exp_pos _).le
  have hy1 : y < 1 := hy_le_b.trans_lt (Real.exp_lt_one_iff.2 (by linarith))
  have hlog_y : Real.log y = -F 1 - Real.log x := by
    dsimp [y]; rw [Real.log_div (Real.exp_pos _).ne' hx0.ne', Real.log_exp]
  have hlog_a : -F' 1 ≤ Real.log x := by
    calc -F' 1 = Real.log (Real.exp (-F' 1)) := (Real.log_exp _).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxa
  have hlog_b : Real.log x ≤ -(F 1 - F' 1) := by
    calc Real.log x ≤ Real.log (Real.exp (-(F 1 - F' 1))) := Real.log_le_log hx0 hxb
      _ = -(F 1 - F' 1) := Real.log_exp _
  have h1 : ∀ s ∈ Ioc (0 : ℝ) 1, F s + Real.log x + s * Real.log y ≤ 0 := by
    intro s hs
    have htan := tangent_le_of_antitone_deriv F F' hF_deriv hF'_anti ⟨zero_lt_one, le_rfl⟩ hs
    rw [hlog_y]
    have h1ms : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    nlinarith
  have h2 : ∀ s ∈ Ioc (0 : ℝ) 1, F s + s * Real.log x + Real.log y ≤ 0 := by
    intro s hs
    have htan := tangent_le_of_antitone_deriv F F' hF_deriv hF'_anti ⟨zero_lt_one, le_rfl⟩ hs
    rw [hlog_y]
    have h1ms : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    nlinarith
  exact ⟨hy0, hy1, inR_of_ramsey_bound F hRam hx0 hx1 hy0 hy1 h1 h2⟩

end Erdos627AFM

/- ==================== Section: IntervalArith.lean ====================-/
namespace Erdos627AFM

open Real Finset

/-- Fixed-point scale D = 10^9 for verified integer interval arithmetic. -/
def ivScale : ℤ := 1000000000

lemma ivScale_pos : (0 : ℝ) < (ivScale : ℝ) := by unfold ivScale; norm_num

lemma ivScale_pos_int : (0 : ℤ) < ivScale := by unfold ivScale; decide

/-- Floor division a / d for d > 0 (Int.ediv always rounds toward -∞). -/
def divLo (a d : ℤ) : ℤ := a / d

/-- Ceiling division ⌈a / d⌉ for d > 0. -/
def divHi (a d : ℤ) : ℤ := (a + d - 1) / d

lemma divLo_le (a d : ℤ) (hd : 0 < d) : ((divLo a d : ℤ) : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hd_r]
  have h := Int.mul_ediv_add_emod a d
  have hmod : 0 ≤ a % d := Int.emod_nonneg a hd.ne'
  have hle : (a / d) * d ≤ a := by linarith
  unfold divLo
  exact_mod_cast hle

lemma le_divHi (a d : ℤ) (hd : 0 < d) : (a : ℝ) / (d : ℝ) ≤ ((divHi a d : ℤ) : ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_iff₀ hd_r]
  have h := Int.mul_ediv_add_emod (a + d - 1) d
  have hmod : (a + d - 1) % d < d := Int.emod_lt_of_pos _ hd
  have hle : a ≤ ((a + d - 1) / d) * d := by linarith
  unfold divHi
  exact_mod_cast hle

/-- Fixed-point interval [lo / ivScale, hi / ivScale]. -/
structure Iv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

/-- Membership of a real number in an interval. -/
def Iv.Mem (I : Iv) (x : ℝ) : Prop :=
  (I.lo : ℝ) / (ivScale : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) / (ivScale : ℝ)

def Iv.ofScaled (n : ℤ) : Iv := ⟨n, n⟩

def Iv.ofInt (n : ℤ) : Iv := ⟨n * ivScale, n * ivScale⟩

def Iv.ofRat (p q : ℤ) : Iv := ⟨divLo (p * ivScale) q, divHi (p * ivScale) q⟩

def Iv.add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

def Iv.neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩

def Iv.sub (I J : Iv) : Iv := ⟨I.lo - J.hi, I.hi - J.lo⟩

def Iv.mul (I J : Iv) : Iv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨divLo (min (min a b) (min c d)) ivScale, divHi (max (max a b) (max c d)) ivScale⟩

def Iv.sqNonneg (I : Iv) : Iv :=
  ⟨divLo (I.lo * I.lo) ivScale, divHi (I.hi * I.hi) ivScale⟩

def Iv.invPos (I : Iv) : Iv :=
  ⟨divLo (ivScale * ivScale) I.hi, divHi (ivScale * ivScale) I.lo⟩

def Iv.divPos (I J : Iv) : Iv := Iv.mul I (Iv.invPos J)

def Iv.scaleDiv (I : Iv) (k : ℤ) : Iv :=
  ⟨divLo I.lo k, divHi I.hi k⟩

def Iv.widen (I : Iv) (e : ℤ) : Iv := ⟨I.lo - e, I.hi + e⟩

lemma Iv.mem_ofInt (n : ℤ) : (Iv.ofInt n).Mem (n : ℝ) := by
  have hD : (ivScale : ℝ) ≠ 0 := ivScale_pos.ne'
  simp [Iv.Mem, Iv.ofInt, mul_div_cancel_right₀ _ hD]

lemma Iv.mem_ofRat {p q : ℤ} (hq : 0 < q) : (Iv.ofRat p q).Mem ((p : ℝ) / (q : ℝ)) := by
  have hD := ivScale_pos
  refine ⟨?_, ?_⟩
  · dsimp [Iv.ofRat]
    have h1 := divLo_le (p * ivScale) q hq
    rw [div_le_iff₀ hD]
    have h2 : ((divLo (p * ivScale) q : ℤ) : ℝ) ≤ (p : ℝ) * (ivScale : ℝ) / (q : ℝ) := by
      simpa using h1
    linarith [show (p : ℝ) / (q : ℝ) * (ivScale : ℝ) = (p : ℝ) * (ivScale : ℝ) / (q : ℝ) by ring]
  · dsimp [Iv.ofRat]
    have h1 := le_divHi (p * ivScale) q hq
    rw [le_div_iff₀ hD]
    have h2 : (p : ℝ) * (ivScale : ℝ) / (q : ℝ) ≤ ((divHi (p * ivScale) q : ℤ) : ℝ) := by
      simpa using h1
    linarith [show (p : ℝ) / (q : ℝ) * (ivScale : ℝ) = (p : ℝ) * (ivScale : ℝ) / (q : ℝ) by ring]

lemma Iv.mem_add {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x + y) := by
  refine ⟨?_, ?_⟩ <;> simp only [Iv.add, Int.cast_add, add_div] <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma Iv.mem_neg {I : Iv} {x : ℝ} (hx : I.Mem x) : (I.neg).Mem (-x) := by
  refine ⟨?_, ?_⟩ <;> simp only [Iv.neg, Int.cast_neg, neg_div] <;> linarith [hx.1, hx.2]

lemma Iv.mem_sub {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x - y) := by
  refine ⟨?_, ?_⟩ <;> simp only [Iv.sub, Int.cast_sub, sub_div] <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma Iv.mem_mul {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by
  have hD := ivScale_pos
  set a := (I.lo : ℝ) / (ivScale : ℝ)
  set b := (I.hi : ℝ) / (ivScale : ℝ)
  set c := (J.lo : ℝ) / (ivScale : ℝ)
  set d := (J.hi : ℝ) / (ivScale : ℝ)
  have hmin : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
    by_cases hy0 : 0 ≤ y
    · have h1 : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      have h2 : min (a * c) (a * d) ≤ a * y := by
        by_cases ha0 : 0 ≤ a
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 ha0)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha0))
      exact ((min_le_left _ _).trans h2).trans h1
    · have h1 : b * y ≤ x * y := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
      have h2 : min (b * c) (b * d) ≤ b * y := by
        by_cases hb0 : 0 ≤ b
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hb0)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb0))
      exact ((min_le_right _ _).trans h2).trans h1
  have hmax : x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    by_cases hy0 : 0 ≤ y
    · have h1 : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
      have h2 : b * y ≤ max (b * c) (b * d) := by
        by_cases hb0 : 0 ≤ b
        · exact (mul_le_mul_of_nonneg_left hy.2 hb0).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans (le_max_left _ _)
      exact h1.trans (h2.trans (le_max_right _ _))
    · have h1 : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
      have h2 : a * y ≤ max (a * c) (a * d) := by
        by_cases ha0 : 0 ≤ a
        · exact (mul_le_mul_of_nonneg_left hy.2 ha0).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans (le_max_left _ _)
      exact h1.trans (h2.trans (le_max_left _ _))
  have hscale_min : ((min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) : ℤ) : ℝ) /
      ((ivScale : ℝ) * (ivScale : ℝ)) = min (min (a * c) (a * d)) (min (b * c) (b * d)) := by
    dsimp [a, b, c, d]
    have hnn : 0 ≤ ((ivScale : ℝ) * (ivScale : ℝ))⁻¹ := inv_nonneg.2 (mul_nonneg hD.le hD.le)
    rw [Int.cast_min, Int.cast_min, Int.cast_min, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul,
        div_eq_mul_inv, min_mul_of_nonneg _ _ hnn, min_mul_of_nonneg _ _ hnn, min_mul_of_nonneg _ _ hnn]
    simp only [← div_eq_mul_inv, mul_div_mul_comm]
  have hscale_max : ((max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)) : ℤ) : ℝ) /
      ((ivScale : ℝ) * (ivScale : ℝ)) = max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    dsimp [a, b, c, d]
    have hnn : 0 ≤ ((ivScale : ℝ) * (ivScale : ℝ))⁻¹ := inv_nonneg.2 (mul_nonneg hD.le hD.le)
    rw [Int.cast_max, Int.cast_max, Int.cast_max, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul,
        div_eq_mul_inv, max_mul_of_nonneg _ _ hnn, max_mul_of_nonneg _ _ hnn, max_mul_of_nonneg _ _ hnn]
    simp only [← div_eq_mul_inv, mul_div_mul_comm]
  refine ⟨?_, ?_⟩
  · dsimp [Iv.mul]
    have h1 := divLo_le (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) ivScale ivScale_pos_int
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    rw [div_div] at h2
    exact (h2.trans_eq hscale_min).trans hmin
  · dsimp [Iv.mul]
    have h1 := le_divHi (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) ivScale ivScale_pos_int
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    rw [div_div] at h2
    exact hmax.trans (hscale_max.symm.trans_le h2)

lemma Iv.mem_sqNonneg {I : Iv} {x : ℝ} (hlo : 0 ≤ I.lo) (hx : I.Mem x) :
    (I.sqNonneg).Mem (x * x) := by
  have hD := ivScale_pos
  have hlo_r : (0 : ℝ) ≤ (I.lo : ℝ) / (ivScale : ℝ) := div_nonneg (by exact_mod_cast hlo) hD.le
  have hx0 : 0 ≤ x := hlo_r.trans hx.1
  refine ⟨?_, ?_⟩
  · dsimp [Iv.sqNonneg]
    have h1 := divLo_le (I.lo * I.lo) ivScale ivScale_pos_int
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    rw [div_div] at h2
    have h3 : ((I.lo * I.lo : ℤ) : ℝ) / ((ivScale : ℝ) * (ivScale : ℝ)) =
        ((I.lo : ℝ) / (ivScale : ℝ)) * ((I.lo : ℝ) / (ivScale : ℝ)) := by push_cast; ring
    rw [h3] at h2
    exact h2.trans (mul_le_mul hx.1 hx.1 hlo_r hx0)
  · dsimp [Iv.sqNonneg]
    have h1 := le_divHi (I.hi * I.hi) ivScale ivScale_pos_int
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    rw [div_div] at h2
    have h3 : ((I.hi * I.hi : ℤ) : ℝ) / ((ivScale : ℝ) * (ivScale : ℝ)) =
        ((I.hi : ℝ) / (ivScale : ℝ)) * ((I.hi : ℝ) / (ivScale : ℝ)) := by push_cast; ring
    rw [h3] at h2
    exact (mul_le_mul hx.2 hx.2 hx0 (hx0.trans hx.2)).trans h2

lemma Iv.mem_invPos {I : Iv} {x : ℝ} (hlo : 0 < I.lo) (hx : I.Mem x) :
    (I.invPos).Mem x⁻¹ := by
  have hD := ivScale_pos
  have hlo_r : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
  have hlo_d : 0 < (I.lo : ℝ) / (ivScale : ℝ) := div_pos hlo_r hD
  have hx0 : 0 < x := hlo_d.trans_le hx.1
  have hhi_r : (0 : ℝ) < (I.hi : ℝ) := by
    have : (I.lo : ℝ) / (ivScale : ℝ) ≤ (I.hi : ℝ) / (ivScale : ℝ) := hx.1.trans hx.2
    have := (div_le_div_iff_of_pos_right hD).1 this
    linarith
  have hhi : 0 < I.hi := by exact_mod_cast hhi_r
  refine ⟨?_, ?_⟩
  · dsimp [Iv.invPos]
    have h1 := divLo_le (ivScale * ivScale) I.hi hhi
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    have h3 : ((ivScale * ivScale : ℤ) : ℝ) / (I.hi : ℝ) / (ivScale : ℝ) =
        ((I.hi : ℝ) / (ivScale : ℝ))⁻¹ := by push_cast; field_simp [hD.ne', hhi_r.ne']
    rw [h3] at h2
    exact h2.trans (inv_anti₀ hx0 hx.2)
  · dsimp [Iv.invPos]
    have h1 := le_divHi (ivScale * ivScale) I.lo hlo
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    have h3 : ((ivScale * ivScale : ℤ) : ℝ) / (I.lo : ℝ) / (ivScale : ℝ) =
        ((I.lo : ℝ) / (ivScale : ℝ))⁻¹ := by push_cast; field_simp [hD.ne', hlo_r.ne']
    rw [h3] at h2
    exact (inv_anti₀ hlo_d hx.1).trans h2

lemma Iv.mem_divPos {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hlo : 0 < J.lo) (hy : J.Mem y) :
    (I.divPos J).Mem (x / y) := by
  rw [div_eq_mul_inv]
  exact Iv.mem_mul hx (Iv.mem_invPos hlo hy)

lemma Iv.mem_scaleDiv {I : Iv} {k : ℤ} (hk : 0 < k) {x : ℝ} (hx : I.Mem x) :
    (I.scaleDiv k).Mem (x / (k : ℝ)) := by
  have hD := ivScale_pos
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · dsimp [Iv.scaleDiv]
    have h1 := divLo_le I.lo k hk
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    have h3 : (I.lo : ℝ) / (k : ℝ) / (ivScale : ℝ) = ((I.lo : ℝ) / (ivScale : ℝ)) / (k : ℝ) := by ring
    rw [h3] at h2
    exact h2.trans (div_le_div_of_nonneg_right hx.1 hkr.le)
  · dsimp [Iv.scaleDiv]
    have h1 := le_divHi I.hi k hk
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    have h3 : (I.hi : ℝ) / (k : ℝ) / (ivScale : ℝ) = ((I.hi : ℝ) / (ivScale : ℝ)) / (k : ℝ) := by ring
    rw [h3] at h2
    exact (div_le_div_of_nonneg_right hx.2 hkr.le).trans h2

lemma Iv.mem_widen {I : Iv} {e : ℤ} {x y : ℝ} (hx : I.Mem x)
    (he : |y - x| ≤ (e : ℝ) / (ivScale : ℝ)) : (I.widen e).Mem y := by
  rw [abs_le] at he
  refine ⟨?_, ?_⟩ <;> simp only [Iv.widen, Int.cast_sub, Int.cast_add, sub_div, add_div] <;>
    linarith [hx.1, hx.2, he.1, he.2]

/-- Taylor polynomial ∑_{i=0}^{9} u^i / i! evaluated via Horner's method in interval arithmetic. -/
def Iv.expTaylor10 (U : Iv) : Iv :=
  let one := Iv.ofInt 1
  let s9 := Iv.add one (Iv.scaleDiv U 9)
  let s8 := Iv.add one (Iv.scaleDiv (Iv.mul U s9) 8)
  let s7 := Iv.add one (Iv.scaleDiv (Iv.mul U s8) 7)
  let s6 := Iv.add one (Iv.scaleDiv (Iv.mul U s7) 6)
  let s5 := Iv.add one (Iv.scaleDiv (Iv.mul U s6) 5)
  let s4 := Iv.add one (Iv.scaleDiv (Iv.mul U s5) 4)
  let s3 := Iv.add one (Iv.scaleDiv (Iv.mul U s4) 3)
  let s2 := Iv.add one (Iv.scaleDiv (Iv.mul U s3) 2)
  Iv.add one (Iv.mul U s2)

lemma Iv.mem_expTaylor10 {U : Iv} {u : ℝ} (hu : U.Mem u) :
    (Iv.expTaylor10 U).Mem (∑ i ∈ Finset.range 10, u ^ i / (Nat.factorial i : ℝ)) := by
  have hhorner : ∑ i ∈ Finset.range 10, u ^ i / (Nat.factorial i : ℝ) =
      1 + u * (1 + u * (1 + u * (1 + u * (1 + u * (1 + u * (1 + u * (1 + u * (1 + u / 9) / 8) / 7) / 6) / 5) / 4) / 3) / 2) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num; ring
  rw [hhorner]
  unfold Iv.expTaylor10
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have h9 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 9) (by norm_num) hu)
  have h8 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 8) (by norm_num) (Iv.mem_mul hu h9))
  have h7 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 7) (by norm_num) (Iv.mem_mul hu h8))
  have h6 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 6) (by norm_num) (Iv.mem_mul hu h7))
  have h5 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 5) (by norm_num) (Iv.mem_mul hu h6))
  have h4 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 4) (by norm_num) (Iv.mem_mul hu h5))
  have h3 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 3) (by norm_num) (Iv.mem_mul hu h4))
  have h2 := Iv.mem_add h1 (Iv.mem_scaleDiv (k := 2) (by norm_num) (Iv.mem_mul hu h3))
  simpa using Iv.mem_add h1 (Iv.mem_mul hu h2)

/-- Interval bound for exp(a / D) valid whenever |a| ≤ 8 * D (so |a / (16 * D)| ≤ 1/2). -/
def Iv.expPt (a : ℤ) : Iv :=
  let U : Iv := ⟨divLo a 16, divHi a 16⟩
  let base := (Iv.expTaylor10 U).widen 1
  let b1 := Iv.mul base base
  let b2 := Iv.mul b1 b1
  let b3 := Iv.mul b2 b2
  Iv.mul b3 b3

lemma Iv.mem_expPt {a : ℤ} (ha : |a| ≤ 8 * ivScale) :
    (Iv.expPt a).Mem (Real.exp ((a : ℝ) / (ivScale : ℝ))) := by
  have hD := ivScale_pos
  set u : ℝ := (a : ℝ) / (ivScale : ℝ) / 16
  have hu_abs : |u| ≤ 1 / 2 := by
    have ha_r : |(a : ℝ)| ≤ 8 * (ivScale : ℝ) := by exact_mod_cast ha
    dsimp [u]
    rw [abs_div, abs_div, abs_of_pos hD, abs_of_pos (show (0 : ℝ) < 16 by norm_num)]
    rw [div_le_iff₀ (show (0 : ℝ) < 16 by norm_num), div_le_iff₀ hD]
    linarith
  have hU : (⟨divLo a 16, divHi a 16⟩ : Iv).Mem u := by
    have h1 := Iv.mem_scaleDiv (I := Iv.ofScaled a) (k := 16) (by norm_num)
      (show (Iv.ofScaled a).Mem ((a : ℝ) / (ivScale : ℝ)) from ⟨le_rfl, le_rfl⟩)
    exact h1
  have htay := Iv.mem_expTaylor10 hU
  have herr : |Real.exp u - ∑ i ∈ Finset.range 10, u ^ i / (Nat.factorial i : ℝ)| ≤ (1 : ℝ) / (ivScale : ℝ) := by
    have hb := Real.exp_bound (x := u) (n := 10) (by linarith) (by norm_num)
    have hpow : |u| ^ 10 ≤ (1 / 2 : ℝ) ^ 10 := pow_le_pow_left₀ (abs_nonneg u) hu_abs 10
    have hnum : (1 / 2 : ℝ) ^ 10 * ((10 + 1 : ℕ) / ((Nat.factorial 10 : ℝ) * 10)) ≤ (1 : ℝ) / (ivScale : ℝ) := by
      unfold ivScale
      norm_num [Nat.factorial]
    have hfac_nn : (0 : ℝ) ≤ (10 + 1 : ℕ) / ((Nat.factorial 10 : ℝ) * 10) := by positivity
    exact hb.trans ((mul_le_mul_of_nonneg_right hpow hfac_nn).trans hnum)
  have hbase : ((Iv.expTaylor10 ⟨divLo a 16, divHi a 16⟩).widen 1).Mem (Real.exp u) :=
    Iv.mem_widen htay (by simpa using herr)
  have h1 := Iv.mem_mul hbase hbase
  have h2 := Iv.mem_mul h1 h1
  have h3 := Iv.mem_mul h2 h2
  have h4 := Iv.mem_mul h3 h3
  have hexp_eq : Real.exp u * Real.exp u * (Real.exp u * Real.exp u) *
      (Real.exp u * Real.exp u * (Real.exp u * Real.exp u)) *
      (Real.exp u * Real.exp u * (Real.exp u * Real.exp u) *
        (Real.exp u * Real.exp u * (Real.exp u * Real.exp u))) =
      Real.exp ((a : ℝ) / (ivScale : ℝ)) := by
    simp only [← Real.exp_add]
    congr 1; dsimp [u]; ring
  rw [← hexp_eq]
  exact h4

/-- Interval bound for exp on an interval I (valid when |I.lo| ≤ 8 * D and |I.hi| ≤ 8 * D). -/
def Iv.exp (I : Iv) : Iv :=
  ⟨(Iv.expPt I.lo).lo, (Iv.expPt I.hi).hi⟩

lemma Iv.mem_exp {I : Iv} {x : ℝ} (hlo : |I.lo| ≤ 8 * ivScale) (hhi : |I.hi| ≤ 8 * ivScale)
    (hx : I.Mem x) : (I.exp).Mem (Real.exp x) := by
  have h1 := Iv.mem_expPt hlo
  have h2 := Iv.mem_expPt hhi
  exact ⟨h1.1.trans (Real.exp_le_exp.2 hx.1), (Real.exp_le_exp.2 hx.2).trans h2.2⟩

/-- Odd Taylor series 2 * (z + z^3/3 + z^5/5 + z^7/7 + z^9/9 + z^11/11) for log((1+z)/(1-z)). -/
def Iv.logOdd11 (Z : Iv) : Iv :=
  let Z2 := Iv.mul Z Z
  let t11 := Iv.ofRat 1 11
  let t9 := Iv.add (Iv.ofRat 1 9) (Iv.mul Z2 t11)
  let t7 := Iv.add (Iv.ofRat 1 7) (Iv.mul Z2 t9)
  let t5 := Iv.add (Iv.ofRat 1 5) (Iv.mul Z2 t7)
  let t3 := Iv.add (Iv.ofRat 1 3) (Iv.mul Z2 t5)
  let t1 := Iv.add (Iv.ofInt 1) (Iv.mul Z2 t3)
  Iv.mul (Iv.ofInt 2) (Iv.mul Z t1)

lemma Iv.mem_logOdd11 {Z : Iv} {z : ℝ} (hz : Z.Mem z) :
    (Iv.logOdd11 Z).Mem (2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9 + z ^ 11 / 11)) := by
  have heq : 2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9 + z ^ 11 / 11) =
      (2 : ℤ) * (z * ((1 : ℤ) + (z * z) * ((1 : ℝ) / 3 + (z * z) * ((1 : ℝ) / 5 +
        (z * z) * ((1 : ℝ) / 7 + (z * z) * ((1 : ℝ) / 9 + (z * z) * ((1 : ℝ) / 11))))))) := by
    push_cast; ring
  rw [heq]
  unfold Iv.logOdd11
  have hZ2 := Iv.mem_mul hz hz
  have h11 := Iv.mem_ofRat (p := 1) (q := 11) (by norm_num)
  have h9 := Iv.mem_add (Iv.mem_ofRat (p := 1) (q := 9) (by norm_num)) (Iv.mem_mul hZ2 h11)
  have h7 := Iv.mem_add (Iv.mem_ofRat (p := 1) (q := 7) (by norm_num)) (Iv.mem_mul hZ2 h9)
  have h5 := Iv.mem_add (Iv.mem_ofRat (p := 1) (q := 5) (by norm_num)) (Iv.mem_mul hZ2 h7)
  have h3 := Iv.mem_add (Iv.mem_ofRat (p := 1) (q := 3) (by norm_num)) (Iv.mem_mul hZ2 h5)
  have h1 := Iv.mem_add (Iv.mem_ofInt 1) (Iv.mem_mul hZ2 h3)
  have hm := Iv.mem_mul hz h1
  simpa using Iv.mem_mul (Iv.mem_ofInt 2) hm

/-- Interval bound for log(y) when y ∈ Y ⊆ [2/3, 4/3] (so |(y-1)/(y+1)| ≤ 1/5). -/
def Iv.logNearOne (Y : Iv) : Iv :=
  let one := Iv.ofInt 1
  let Z := Iv.divPos (Iv.sub Y one) (Iv.add Y one)
  (Iv.logOdd11 Z).widen 3

lemma Iv.mem_logNearOne {Y : Iv} {y : ℝ} (hY : Y.Mem y)
    (hlo : 2 * ivScale ≤ 3 * Y.lo) (hhi : 3 * Y.hi ≤ 4 * ivScale) :
    (Iv.logNearOne Y).Mem (Real.log y) := by
  have hD := ivScale_pos
  have hYlo_pos : 0 < Y.lo := by have := ivScale_pos_int; omega
  have hy_ge : (2 : ℝ) / 3 ≤ y := by
    have h1 : (2 : ℝ) * (ivScale : ℝ) ≤ 3 * (Y.lo : ℝ) := by exact_mod_cast hlo
    have h2 : (2 : ℝ) / 3 ≤ (Y.lo : ℝ) / (ivScale : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hD]; linarith
    exact h2.trans hY.1
  have hy_le : y ≤ 4 / 3 := by
    have h1 : 3 * (Y.hi : ℝ) ≤ 4 * (ivScale : ℝ) := by exact_mod_cast hhi
    have h2 : (Y.hi : ℝ) / (ivScale : ℝ) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ hD (by norm_num)]; linarith
    exact hY.2.trans h2
  have hy_pos : 0 < y := by linarith
  set z : ℝ := (y - 1) / (y + 1)
  have hz_abs : |z| ≤ 1 / 5 := by
    dsimp [z]; rw [abs_div, abs_of_pos (by linarith : 0 < y + 1), div_le_iff₀ (by linarith)]
    rw [abs_le]; constructor <;> linarith
  have hz_lt1 : |z| < 1 := by linarith
  have hlog_eq : Real.log y = Real.log (1 + z) - Real.log (1 - z) := by
    have h1 : 0 < 1 + z := by rw [abs_le] at hz_abs; linarith
    have h2 : 0 < 1 - z := by rw [abs_le] at hz_abs; linarith
    have h3 : (1 + z) / (1 - z) = y := by dsimp [z]; field_simp [(show y + 1 ≠ 0 by linarith)]; ring
    rw [← Real.log_div h1.ne' h2.ne', h3]
  -- Apply Real.abs_log_sub_add_sum_range_le to z and -z with n = 12
  have hneg : |Real.log (1 - z) + ∑ i ∈ Finset.range 12, z ^ (i + 1) / (i + 1 : ℕ)| ≤
      |z| ^ 13 / (1 - |z|) := by
    have h := Real.abs_log_sub_add_sum_range_le hz_lt1 12
    rw [add_comm] at h
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hpos : |Real.log (1 - (-z)) + ∑ i ∈ Finset.range 12, (-z) ^ (i + 1) / (i + 1 : ℕ)| ≤
      |-z| ^ 13 / (1 - |-z|) := by
    have h := Real.abs_log_sub_add_sum_range_le (by simpa using hz_lt1 : |-z| < 1) 12
    rw [add_comm] at h
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hsum_diff : (∑ i ∈ Finset.range 12, z ^ (i + 1) / (i + 1 : ℕ)) -
      (∑ i ∈ Finset.range 12, (-z) ^ (i + 1) / (i + 1 : ℕ)) =
      2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9 + z ^ 11 / 11) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    push_cast; ring
  have herr : |Real.log y - 2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9 + z ^ 11 / 11)| ≤
      (3 : ℝ) / (ivScale : ℝ) := by
    rw [hlog_eq, ← hsum_diff]
    have hsplit : Real.log (1 + z) - Real.log (1 - z) -
        ((∑ i ∈ Finset.range 12, z ^ (i + 1) / (i + 1 : ℕ)) -
         (∑ i ∈ Finset.range 12, (-z) ^ (i + 1) / (i + 1 : ℕ))) =
        (Real.log (1 - (-z)) + ∑ i ∈ Finset.range 12, (-z) ^ (i + 1) / (i + 1 : ℕ)) -
        (Real.log (1 - z) + ∑ i ∈ Finset.range 12, z ^ (i + 1) / (i + 1 : ℕ)) := by
      have : (1 : ℝ) - (-z) = 1 + z := by ring
      rw [this]; ring
    rw [hsplit]
    have htri := abs_sub (Real.log (1 - (-z)) + ∑ i ∈ Finset.range 12, (-z) ^ (i + 1) / (i + 1 : ℕ))
      (Real.log (1 - z) + ∑ i ∈ Finset.range 12, z ^ (i + 1) / (i + 1 : ℕ))
    rw [abs_neg] at hpos
    have hbound1 : |z| ^ 13 / (1 - |z|) ≤ (1 / 5 : ℝ) ^ 13 / (4 / 5) := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg z) hz_abs 13) (by norm_num) (by linarith)
    have hnum : 2 * ((1 / 5 : ℝ) ^ 13 / (4 / 5)) ≤ (3 : ℝ) / (ivScale : ℝ) := by
      unfold ivScale; norm_num
    linarith
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have hadd_lo : 0 < (Iv.add Y (Iv.ofInt 1)).lo := by
    dsimp [Iv.add, Iv.ofInt]; have := ivScale_pos_int; omega
  have hZ : (Iv.divPos (Iv.sub Y (Iv.ofInt 1)) (Iv.add Y (Iv.ofInt 1))).Mem z :=
    Iv.mem_divPos (Iv.mem_sub hY h1) hadd_lo (Iv.mem_add hY h1)
  have hodd := Iv.mem_logOdd11 hZ
  exact Iv.mem_widen hodd (by simpa using herr)

/-- Range reduction for log(a / D): find k ∈ ℤ and interval Y ⊆ [2/3, 4/3] containing (a / D) * 2^k. -/
def logReduceAux : ℕ → ℤ → ℤ → ℤ × Iv
  | 0, k, a => (k, ⟨a, a⟩)
  | fuel + 1, k, a =>
    if 3 * a < 2 * ivScale then logReduceAux fuel (k + 1) (2 * a)
    else if 4 * ivScale < 3 * a then logReduceAux fuel (k - 1) (divLo a 2)
    else (k, ⟨a, a⟩)

/-- Range reduction keeping exact upper/lower interval Y containing (a / D) * 2^k. -/
def logReduceIv : ℕ → ℤ → Iv → ℤ × Iv
  | 0, k, Y => (k, Y)
  | fuel + 1, k, Y =>
    if 3 * Y.lo < 2 * ivScale then logReduceIv fuel (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩
    else if 4 * ivScale < 3 * Y.hi then logReduceIv fuel (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩
    else (k, Y)

def log2Iv : Iv := ⟨693147180, 693147181⟩

lemma mem_log2Iv : log2Iv.Mem (Real.log 2) := by
  refine ⟨?_, ?_⟩ <;> unfold log2Iv ivScale
  · have h := Real.log_two_gt_d9; norm_num; linarith
  · have h := Real.log_two_lt_d9; norm_num; linarith

lemma logReduceIv_spec : ∀ (fuel : ℕ) (k : ℤ) (Y : Iv) (y : ℝ),
    Y.Mem y →
    let res := logReduceIv fuel k Y
    res.2.Mem (y * (2 : ℝ) ^ (res.1 - k)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k Y y hy
    simp [logReduceIv, hy]
  | succ fuel ih =>
    intro k Y y hy
    simp only [logReduceIv]
    split_ifs with h1 h2
    · have hy2 : (⟨2 * Y.lo, 2 * Y.hi⟩ : Iv).Mem (2 * y) := by
        refine ⟨?_, ?_⟩ <;> simp only [Int.cast_mul, Int.cast_ofNat, mul_div_assoc] <;>
          linarith [hy.1, hy.2]
      have hres := ih (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩ (2 * y) hy2
      dsimp only at hres ⊢
      have heq : 2 * y * (2 : ℝ) ^ ((logReduceIv fuel (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩).1 - (k + 1)) =
          y * (2 : ℝ) ^ ((logReduceIv fuel (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩).1 - k) := by
        have hsub : (logReduceIv fuel (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩).1 - k =
            ((logReduceIv fuel (k + 1) ⟨2 * Y.lo, 2 * Y.hi⟩).1 - (k + 1)) + 1 := by omega
        rw [hsub, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      rwa [heq] at hres
    · have hy2 : (⟨divLo Y.lo 2, divHi Y.hi 2⟩ : Iv).Mem (y / 2) :=
        Iv.mem_scaleDiv (k := 2) (by norm_num) hy
      have hres := ih (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩ (y / 2) hy2
      dsimp only at hres ⊢
      have heq : y / 2 * (2 : ℝ) ^ ((logReduceIv fuel (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩).1 - (k - 1)) =
          y * (2 : ℝ) ^ ((logReduceIv fuel (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩).1 - k) := by
        have hsub : (logReduceIv fuel (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩).1 - (k - 1) =
            ((logReduceIv fuel (k - 1) ⟨divLo Y.lo 2, divHi Y.hi 2⟩).1 - k) + 1 := by omega
        rw [hsub, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      rwa [heq] at hres
    · simp [hy]

/-- Verified interval bound for log(a / D) using 20 steps of range reduction. -/
def Iv.logPt (a : ℤ) : Iv :=
  let res := logReduceIv 20 0 ⟨a, a⟩
  Iv.sub (Iv.logNearOne res.2) (Iv.mul (Iv.ofInt res.1) log2Iv)

/-- Check that range reduction succeeded into [2/3, 4/3]. -/
def Iv.logPtOk (a : ℤ) : Bool :=
  let res := logReduceIv 20 0 ⟨a, a⟩
  decide (0 < a ∧ 2 * ivScale ≤ 3 * res.2.lo ∧ 3 * res.2.hi ≤ 4 * ivScale)

lemma Iv.mem_logPt {a : ℤ} (hok : Iv.logPtOk a = true) :
    (Iv.logPt a).Mem (Real.log ((a : ℝ) / (ivScale : ℝ))) := by
  unfold Iv.logPtOk at hok
  rw [decide_eq_true_eq] at hok
  rcases hok with ⟨ha_pos, hlo, hhi⟩
  have hD := ivScale_pos
  have ha_r : (0 : ℝ) < (a : ℝ) / (ivScale : ℝ) := div_pos (by exact_mod_cast ha_pos) hD
  set res := logReduceIv 20 0 ⟨a, a⟩
  have hmem := logReduceIv_spec 20 0 ⟨a, a⟩ ((a : ℝ) / (ivScale : ℝ)) ⟨le_rfl, le_rfl⟩
  simp only [sub_zero] at hmem
  have hnear := Iv.mem_logNearOne hmem hlo hhi
  have hlog_eq : Real.log ((a : ℝ) / (ivScale : ℝ)) =
      Real.log ((a : ℝ) / (ivScale : ℝ) * (2 : ℝ) ^ res.1) - (res.1 : ℝ) * Real.log 2 := by
    rw [Real.log_mul ha_r.ne' (zpow_pos (by norm_num) _).ne', Real.log_zpow]
    ring
  rw [hlog_eq]
  exact Iv.mem_sub hnear (Iv.mem_mul (Iv.mem_ofInt res.1) mem_log2Iv)

def Iv.log (I : Iv) : Iv :=
  ⟨(Iv.logPt I.lo).lo, (Iv.logPt I.hi).hi⟩

def Iv.logOk (I : Iv) : Bool :=
  Iv.logPtOk I.lo && Iv.logPtOk I.hi

lemma Iv.mem_log {I : Iv} {x : ℝ} (hok : Iv.logOk I = true) (hx : I.Mem x) :
    (I.log).Mem (Real.log x) := by
  unfold Iv.logOk at hok
  rw [Bool.and_eq_true] at hok
  have h1 := Iv.mem_logPt hok.1
  have h2 := Iv.mem_logPt hok.2
  have hlo_pos : 0 < I.lo := by
    have h := hok.1; unfold Iv.logPtOk at h; rw [decide_eq_true_eq] at h; exact h.1
  have hlo_r : 0 < (I.lo : ℝ) / (ivScale : ℝ) := div_pos (by exact_mod_cast hlo_pos) ivScale_pos
  have hx0 : 0 < x := hlo_r.trans_le hx.1
  exact ⟨h1.1.trans (Real.log_le_log hlo_r hx.1), (Real.log_le_log hx0 hx.2).trans h2.2⟩

end Erdos627AFM

/- ==================== Section: NumericsBase.lean ====================-/
namespace Erdos627AFM

open Real Set

/-- Binary entropy function h(t) = (1 + t) log(1 + t) - t log t. -/
noncomputable def hEntN (t : ℝ) : ℝ := (1 + t) * Real.log (1 + t) - t * Real.log t

/-- Correction term g_b(t) = (-1/4 t + b t^2 + 2/25 t^3) exp(-t). -/
noncomputable def gFn (b t : ℝ) : ℝ :=
  (-(1 / 4) * t + b * t ^ 2 + (2 / 25) * t ^ 3) * Real.exp (-t)

/-- First derivative of g_b(t). -/
noncomputable def gFn' (b t : ℝ) : ℝ :=
  (-(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3) * Real.exp (-t)

/-- Second derivative of g_b(t). -/
noncomputable def gFn'' (b t : ℝ) : ℝ :=
  (1 / 2 + 2 * b + (23 / 100 - 4 * b) * t + (b - 12 / 25) * t ^ 2 + (2 / 25) * t ^ 3) * Real.exp (-t)

/-- Exponent function F_b(t) = h(t) + g_b(t). -/
noncomputable def FFn (b t : ℝ) : ℝ := hEntN t + gFn b t

/-- First derivative F_b'(t). -/
noncomputable def FFn' (b t : ℝ) : ℝ := Real.log (1 + t) - Real.log t + gFn' b t

/-- Second derivative F_b''(t). -/
noncomputable def FFn'' (b t : ℝ) : ℝ := -(1 / (t * (1 + t))) + gFn'' b t

/-- Base parameter function M_0(t) = t exp(-t). -/
noncomputable def M0Fn (t : ℝ) : ℝ := t * Real.exp (-t)

/-- Derivative M_0'(t) = (1 - t) exp(-t). -/
noncomputable def M0Fn' (t : ℝ) : ℝ := (1 - t) * Real.exp (-t)

/-- Iterated parameter function M_1(t) = t exp(-2/3 t - 3/10 t^2). -/
noncomputable def M1Fn (t : ℝ) : ℝ := t * Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2)

/-- Derivative M_1'(t). -/
noncomputable def M1Fn' (t : ℝ) : ℝ :=
  (1 - (2 / 3) * t - (3 / 5) * t ^ 2) * Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2)

lemma hasDerivAt_hEntN {t : ℝ} (ht : 0 < t) :
    HasDerivAt hEntN (Real.log (1 + t) - Real.log t) t := by
  have h1t : 0 < 1 + t := by linarith
  have hd1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)
  have hd_log1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    simpa using hd1.log h1t.ne'
  have hd_logt : HasDerivAt Real.log (1 / t) t := by simpa [one_div] using Real.hasDerivAt_log ht.ne'
  have hA := hd1.fun_mul hd_log1
  have hB := (hasDerivAt_id t).fun_mul hd_logt
  refine (hA.fun_sub hB).congr_deriv ?_
  simp only [id_eq]
  field_simp [ht.ne', h1t.ne']
  ring

lemma hasDerivAt_gFn (b t : ℝ) : HasDerivAt (gFn b) (gFn' b t) t := by
  have hi := hasDerivAt_id t
  have hp : HasDerivAt (fun s : ℝ => -(1 / 4) * s + b * s ^ 2 + (2 / 25) * s ^ 3)
      (-(1 / 4) + 2 * b * t + (6 / 25) * t ^ 2) t := by
    have h1 := hi.const_mul (-(1 / 4 : ℝ))
    have h2 := (hi.fun_pow 2).const_mul b
    have h3 := (hi.fun_pow 3).const_mul (2 / 25 : ℝ)
    exact ((h1.fun_add h2).fun_add h3).congr_deriv (by simp only [id_eq]; ring)
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using hi.fun_neg.exp
  refine (hp.fun_mul he).congr_deriv ?_
  unfold gFn'; ring

lemma hasDerivAt_gFn' (b t : ℝ) : HasDerivAt (gFn' b) (gFn'' b t) t := by
  have hi := hasDerivAt_id t
  have hp : HasDerivAt (fun s : ℝ => -(1 / 4) + (2 * b + 1 / 4) * s + (6 / 25 - b) * s ^ 2 - (2 / 25) * s ^ 3)
      ((2 * b + 1 / 4) + 2 * (6 / 25 - b) * t - (6 / 25) * t ^ 2) t := by
    have h0 := hasDerivAt_const t (-(1 / 4 : ℝ))
    have h1 := hi.const_mul (2 * b + 1 / 4)
    have h2 := (hi.fun_pow 2).const_mul (6 / 25 - b)
    have h3 := (hi.fun_pow 3).const_mul (2 / 25 : ℝ)
    exact (((h0.fun_add h1).fun_add h2).fun_sub h3).congr_deriv (by simp only [id_eq]; ring)
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using hi.fun_neg.exp
  refine (hp.fun_mul he).congr_deriv ?_
  unfold gFn''; ring

lemma hasDerivAt_FFn (b : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (FFn b) (FFn' b t) t := by
  unfold FFn FFn'
  exact (hasDerivAt_hEntN ht).fun_add (hasDerivAt_gFn b t)

lemma hasDerivAt_FFn' (b : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (FFn' b) (FFn'' b t) t := by
  have h1t : 0 < 1 + t := by linarith
  have hd1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)).log h1t.ne'
    simpa using this
  have hd2 : HasDerivAt Real.log (1 / t) t := by simpa [one_div] using Real.hasDerivAt_log ht.ne'
  refine ((hd1.fun_sub hd2).fun_add (hasDerivAt_gFn' b t)).congr_deriv ?_
  unfold FFn''
  field_simp [ht.ne', h1t.ne']
  ring

lemma hasDerivAt_M0Fn (t : ℝ) : HasDerivAt M0Fn (M0Fn' t) t := by
  have hi := hasDerivAt_id t
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using hi.fun_neg.exp
  refine (hi.fun_mul he).congr_deriv ?_
  unfold M0Fn'; simp only [id_eq]; ring

lemma hasDerivAt_M1Fn (t : ℝ) : HasDerivAt M1Fn (M1Fn' t) t := by
  have hi := hasDerivAt_id t
  have ha : HasDerivAt (fun s : ℝ => -(2 / 3) * s - (3 / 10) * s ^ 2)
      (-(2 / 3) - (3 / 5) * t) t := by
    have h1 := hi.const_mul (-(2 / 3 : ℝ))
    have h2 := (hi.fun_pow 2).const_mul (3 / 10 : ℝ)
    exact (h1.fun_sub h2).congr_deriv (by simp only [id_eq]; ring)
  have he := ha.exp
  refine (hi.fun_mul he).congr_deriv ?_
  unfold M1Fn'; simp only [id_eq]; ring

lemma FFn''_neg {b t : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    FFn'' b t < 0 := by
  unfold FFn'' gFn''
  -- Poly ≤ 0.66 for b ∈ [0.03, 0.08], t ∈ (0, 1], and t(1+t) exp(-t) ≤ 2/e < 1/0.66
  have hpoly : 1 / 2 + 2 * b + (23 / 100 - 4 * b) * t + (b - 12 / 25) * t ^ 2 + (2 / 25) * t ^ 3 ≤ 7 / 10 := by
    have h1 : 1 / 2 + 2 * b ≤ 66 / 100 := by linarith
    have h2 : (23 / 100 - 4 * b) * t ≤ 11 / 100 * t := by nlinarith
    have h3 : (b - 12 / 25) * t ^ 2 + (2 / 25) * t ^ 3 ≤ -(32 / 100) * t ^ 2 := by nlinarith
    nlinarith [sq_nonneg (t - 1 / 5)]
  -- Also t(1 + t) * exp(-t) ≤ 1 (in fact t(1+t) ≤ 1 + t + t^2/2 ≤ exp(t) for t ≤ 1? Wait: t + t^2 ≤ 2, exp(t) ≥ 1 + t + t^2/2!)
  -- Check: 7/10 * t * (1 + t) < 1 + t + t^2 / 2 ≤ exp(t)!
  have hexp_ge : 1 + t + t ^ 2 / 2 ≤ Real.exp t := by
    have h := Real.sum_le_exp_of_nonneg ht0.le 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
    norm_num at h; linarith
  have hlt : (7 / 10 : ℝ) * (t * (1 + t)) < 1 + t + t ^ 2 / 2 := by nlinarith
  have hlt_exp : (7 / 10 : ℝ) * (t * (1 + t)) < Real.exp t := hlt.trans_le hexp_ge
  have hprod : (7 / 10 : ℝ) * Real.exp (-t) < 1 / (t * (1 + t)) := by
    rw [Real.exp_neg, lt_div_iff₀ (mul_pos ht0 (by linarith)), mul_comm, ← mul_assoc,
        mul_comm _ (Real.exp t)⁻¹, mul_assoc, inv_mul_lt_iff₀ (Real.exp_pos t), mul_one]
    linarith
  have h1 : (1 / 2 + 2 * b + (23 / 100 - 4 * b) * t + (b - 12 / 25) * t ^ 2 + (2 / 25) * t ^ 3) * Real.exp (-t) ≤
      (7 / 10 : ℝ) * Real.exp (-t) := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
  linarith

lemma FFn'_anti {b : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25) :
    AntitoneOn (FFn' b) (Ioc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
  · intro t ht; exact (hasDerivAt_FFn' b ht.1).continuousAt.continuousWithinAt
  · intro t ht; exact (hasDerivAt_FFn' b (interior_subset ht).1).differentiableAt.differentiableWithinAt
  · intro t ht
    have h := interior_subset ht
    rw [(hasDerivAt_FFn' b h.1).deriv]
    exact (FFn''_neg hb1 hb2 h.1 h.2).le

lemma FFn_concave {b : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25) :
    ∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Ioc (0 : ℝ) 1, FFn b s ≤ FFn b t + FFn' b t * (s - t) := by
  have hanti := FFn'_anti hb1 hb2
  intro s hs t ht
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · have hcont : ContinuousOn (FFn b) (Icc s t) := fun u hu =>
      (hasDerivAt_FFn b (hs.1.trans_le hu.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ u ∈ Ioo s t, HasDerivAt (FFn b) (FFn' b u) u := fun u hu =>
      hasDerivAt_FFn b (hs.1.trans hu.1)
    obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope (FFn b) (FFn' b) hlt hcont hderiv
    have hdiff : FFn b t - FFn b s = FFn' b c * (t - s) := ((eq_div_iff (sub_pos.2 hlt).ne').1 hsl).symm
    have hfc : FFn' b t ≤ FFn' b c := hanti ⟨hs.1.trans hc.1, hc.2.le.trans ht.2⟩ ht hc.2.le
    nlinarith
  · simp
  · have hcont : ContinuousOn (FFn b) (Icc t s) := fun u hu =>
      (hasDerivAt_FFn b (ht.1.trans_le hu.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ u ∈ Ioo t s, HasDerivAt (FFn b) (FFn' b u) u := fun u hu =>
      hasDerivAt_FFn b (ht.1.trans hu.1)
    obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope (FFn b) (FFn' b) hgt hcont hderiv
    have hdiff : FFn b s - FFn b t = FFn' b c * (s - t) := ((eq_div_iff (sub_pos.2 hgt).ne').1 hsl).symm
    have hfc : FFn' b c ≤ FFn' b t := hanti ht ⟨ht.1.trans hc.1, hc.2.le.trans hs.2⟩ hc.1.le
    nlinarith

lemma FFn'_pos {b t : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < FFn' b t := by
  unfold FFn' gFn'
  have hlog : Real.log 2 ≤ Real.log (1 + t) - Real.log t := by
    rw [← Real.log_div (by linarith) ht0.ne']
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ ht0]; linarith
  have hpoly : -(1 / 4 : ℝ) ≤ -(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3 := by
    nlinarith [sq_nonneg t]
  have hg : -(1 / 4 : ℝ) ≤ (-(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3) * Real.exp (-t) := by
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc -(1 / 4 : ℝ) ≤ -(1 / 4) * Real.exp (-t) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
  linarith [Real.log_two_gt_d9]

lemma FFn_mono {b : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25) :
    MonotoneOn (FFn b) (Ioc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
  · intro t ht; exact (hasDerivAt_FFn b ht.1).continuousAt.continuousWithinAt
  · intro t ht; exact (hasDerivAt_FFn b (interior_subset ht).1).differentiableAt.differentiableWithinAt
  · intro t ht
    have h := interior_subset ht
    rw [(hasDerivAt_FFn b h.1).deriv]
    exact (FFn'_pos hb1 hb2 h.1 h.2).le

lemma FFn_pos {b t : ℝ} (hb1 : 3 / 100 ≤ b) (_hb2 : b ≤ 2 / 25) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ FFn b t := by
  unfold FFn hEntN gFn
  have h1t_log : t ≤ (1 + t) * Real.log (1 + t) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + t by linarith)
    have h2 : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [(show 1 + t ≠ 0 by linarith)]; ring
    rw [h2] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + t by linarith)
    rwa [mul_div_cancel₀ _ (show 1 + t ≠ 0 by linarith)] at hmul
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hg : -(1 / 4 : ℝ) * t ≤ (-(1 / 4) * t + b * t ^ 2 + (2 / 25) * t ^ 3) * Real.exp (-t) := by
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hp : -(1 / 4) * t ≤ -(1 / 4) * t + b * t ^ 2 + (2 / 25) * t ^ 3 := by nlinarith
    calc -(1 / 4) * t ≤ (-(1 / 4) * t) * Real.exp (-t) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
  nlinarith

/-- Key inequality connecting F_{0.03} to the target constant 0.14 / exp 1:
g_{0.03}(t) ≤ -(0.14 / exp 1) * t for all t ∈ (0, 1]. -/
lemma gFn_003_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    gFn (3 / 100) t ≤ -((14 / 100 : ℝ) / Real.exp 1) * t := by
  let q : ℝ → ℝ := fun s => (-(1 / 4) + (3 / 100) * s + (2 / 25) * s ^ 2) * Real.exp (-s)
  have hq_eq : gFn (3 / 100) t = t * q t := by unfold gFn; dsimp [q]; ring
  have hq1 : q 1 = -((14 / 100 : ℝ) / Real.exp 1) := by
    dsimp [q]; rw [Real.exp_neg]; ring
  have hq_mono : MonotoneOn q (Icc 0 1) := by
    have hd : ∀ s : ℝ, HasDerivAt q ((28 / 100 + 13 / 100 * s - 8 / 100 * s ^ 2) * Real.exp (-s)) s := by
      intro s
      have hi := hasDerivAt_id s
      have hp : HasDerivAt (fun u : ℝ => -(1 / 4) + (3 / 100) * u + (2 / 25) * u ^ 2)
          (3 / 100 + 4 / 25 * s) s := by
        have h0 := hasDerivAt_const s (-(1 / 4 : ℝ))
        have h1 := hi.const_mul (3 / 100 : ℝ)
        have h2 := (hi.fun_pow 2).const_mul (2 / 25 : ℝ)
        exact ((h0.fun_add h1).fun_add h2).congr_deriv (by simp only [id_eq]; ring)
      have he : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-s)) s := by
        simpa using hi.fun_neg.exp
      exact (hp.fun_mul he).congr_deriv (by ring)
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      have h := interior_subset hs
      rw [(hd s).deriv]
      apply mul_nonneg _ (Real.exp_pos _).le
      nlinarith [h.1, h.2]
  have hle : q t ≤ q 1 := hq_mono ⟨ht0.le, ht1⟩ ⟨by norm_num, le_rfl⟩ ht1
  rw [hq_eq, ← hq1, mul_comm (q 1) t]
  exact mul_le_mul_of_nonneg_left hle ht0.le

set_option maxHeartbeats 600000 in
/-- Elementary analytic bound for small t ∈ (0, 1/250] covering BOTH F_{0.08} (with M_0)
and F_{0.03} (with M_1) using the plain Erdős-Szekeres choice y = 1 - X. -/
lemma small_t_phi_pos {b t m : ℝ} (hb1 : 3 / 100 ≤ b) (hb2 : b ≤ 2 / 25)
    (ht0 : 0 < t) (ht_le : t ≤ 1 / 250)
    (hm_lo : t * Real.exp (-t) ≤ m) (hm_hi : m ≤ t) :
    let X := (1 - Real.exp (-FFn' b t)) ^ (1 / (1 - m)) * (1 - m)
    0 < X ∧ X < 1 ∧ -(Real.log X + t * Real.log m + t * Real.log (1 - X)) / 2 < FFn b t := by
  have hm0 : 0 < m := (mul_pos ht0 (Real.exp_pos _)).trans_le hm_lo
  have hm1 : m < 1 := by linarith
  have h1m : 0 < 1 - m := by linarith
  have hFp_pos : 0 < FFn' b t := FFn'_pos hb1 hb2 ht0 (by linarith)
  set q : ℝ := Real.exp (-FFn' b t)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h1q : 0 < 1 - q := by linarith
  set X : ℝ := (1 - q) ^ (1 / (1 - m)) * (1 - m)
  have hX0 : 0 < X := mul_pos (Real.rpow_pos_of_pos h1q _) h1m
  have hX_le_prod : X ≤ (1 - q) * (1 - m) := by
    have hexp_ge1 : 1 ≤ 1 / (1 - m) := (one_le_div h1m).2 (by linarith)
    have hrpow : (1 - q) ^ (1 / (1 - m)) ≤ (1 - q) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h1q (by linarith) hexp_ge1
    rw [Real.rpow_one] at hrpow
    exact mul_le_mul_of_nonneg_right hrpow h1m.le
  have hX1 : X < 1 := by nlinarith
  refine ⟨hX0, hX1, ?_⟩
  -- Need: 0 < 2 * FFn b t + log X + t * log m + t * log (1 - X)
  suffices h : 0 < 2 * FFn b t + Real.log X + t * Real.log m + t * Real.log (1 - X) by linarith
  -- Step 1: FFn b t ≥ 3/4 * t - t * log t
  have hF_lb : (3 / 4 : ℝ) * t - t * Real.log t ≤ FFn b t := by
    unfold FFn hEntN gFn
    have h1t_log : t ≤ (1 + t) * Real.log (1 + t) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + t by linarith)
      have h2 : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [(show 1 + t ≠ 0 by linarith)]; ring
      rw [h2] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + t by linarith)
      rwa [mul_div_cancel₀ _ (show 1 + t ≠ 0 by linarith)] at hmul
    have hg : -(1 / 4 : ℝ) * t ≤ (-(1 / 4) * t + b * t ^ 2 + (2 / 25) * t ^ 3) * Real.exp (-t) := by
      have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have hp : -(1 / 4) * t ≤ -(1 / 4) * t + b * t ^ 2 + (2 / 25) * t ^ 3 := by nlinarith
      calc -(1 / 4) * t ≤ (-(1 / 4) * t) * Real.exp (-t) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    linarith
  -- Step 2: Bounds on gFn' b t ∈ [-1/4, -247/1000]
  have hgp_lo : -(1 / 4 : ℝ) ≤ gFn' b t := by
    unfold gFn'
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hp : -(1 / 4 : ℝ) ≤ -(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3 := by
      nlinarith [sq_nonneg t]
    calc -(1 / 4 : ℝ) ≤ -(1 / 4) * Real.exp (-t) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
  have hgp_hi : gFn' b t ≤ -(247 / 1000 : ℝ) := by
    unfold gFn'
    have he_lo : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    have hp : -(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3 ≤ -(2483 / 10000 : ℝ) := by
      nlinarith [sq_nonneg t]
    have h1 : (-(1 / 4) + (2 * b + 1 / 4) * t + (6 / 25 - b) * t ^ 2 - (2 / 25) * t ^ 3) * Real.exp (-t) ≤
        (-(2483 / 10000 : ℝ)) * Real.exp (-t) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    have h2 : (-(2483 / 10000 : ℝ)) * Real.exp (-t) ≤ -(2483 / 10000 : ℝ) * (1 - t) := by nlinarith
    linarith
  -- Step 3: Bounds on q = (t / (1 + t)) * exp(-gFn' b t)
  have hq_eq : q = t / (1 + t) * Real.exp (-gFn' b t) := by
    dsimp [q]; unfold FFn'
    rw [show -(Real.log (1 + t) - Real.log t + gFn' b t) = Real.log (t / (1 + t)) + (-gFn' b t) by
      rw [Real.log_div ht0.ne' (by linarith)]; ring]
    rw [Real.exp_add, Real.exp_log (div_pos ht0 (by linarith))]
  have hexp_quarter_ub : Real.exp (1 / 4 : ℝ) ≤ 1285 / 1000 := by
    have h := Real.exp_bound (x := (1 / 4 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    rw [abs_le] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hexp_247_lb : (128 / 100 : ℝ) ≤ Real.exp (247 / 1000 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 247 / 1000) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hq_ub : q ≤ (1285 / 1000 : ℝ) * t := by
    rw [hq_eq]
    have h1 : t / (1 + t) ≤ t := div_le_self ht0.le (by linarith)
    have h2 : Real.exp (-gFn' b t) ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 (by linarith)
    calc t / (1 + t) * Real.exp (-gFn' b t)
        ≤ t * Real.exp (1 / 4) := mul_le_mul h1 h2 (Real.exp_pos _).le ht0.le
      _ ≤ t * (1285 / 1000) := mul_le_mul_of_nonneg_left hexp_quarter_ub ht0.le
      _ = (1285 / 1000) * t := mul_comm _ _
  have hq_lb : (1274 / 1000 : ℝ) * t ≤ q := by
    rw [hq_eq]
    have h1 : t / (1 + 1 / 250) ≤ t / (1 + t) :=
      div_le_div_of_nonneg_left ht0.le (by linarith) (by linarith)
    have h2 : (128 / 100 : ℝ) ≤ Real.exp (-gFn' b t) :=
      hexp_247_lb.trans (Real.exp_le_exp.2 (by linarith))
    have h3 : (1274 / 1000 : ℝ) * t ≤ t / (1 + 1 / 250) * (128 / 100) := by
      have : t / (1 + 1 / 250 : ℝ) * (128 / 100) = (320 / 251 : ℝ) * t := by ring
      linarith
    exact h3.trans (mul_le_mul h1 h2 (by norm_num) (div_nonneg ht0.le (by linarith)))
  -- Step 4: Lower bound log X = log(1 - m) + log(1 - q) / (1 - m)
  -- Using elementary log(1 - u) ≥ -u / (1 - u) for u ∈ [0, 1)
  have hlog_one_sub : ∀ u : ℝ, 0 ≤ u → u < 1 → -(u / (1 - u)) ≤ Real.log (1 - u) := by
    intro u hu0 hu1
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - u by linarith)
    have heq : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by field_simp [(show 1 - u ≠ 0 by linarith)]; ring
    rwa [heq] at h
  have hlogX_lb : -(2302 / 1000 : ℝ) * t ≤ Real.log X := by
    have hlogX_eq : Real.log X = Real.log (1 - m) + (1 / (1 - m)) * Real.log (1 - q) := by
      dsimp [X]
      rw [Real.log_mul (Real.rpow_pos_of_pos h1q _).ne' h1m.ne', Real.log_rpow h1q, add_comm]
    rw [hlogX_eq]
    have hlm : -(m / (1 - m)) ≤ Real.log (1 - m) := hlog_one_sub m hm0.le hm1
    have hlm2 : -(250 / 249 : ℝ) * t ≤ -(m / (1 - m)) := by
      have h1 : m / (1 - m) ≤ t / (1 - 1 / 250) :=
        div_le_div₀ ht0.le hm_hi (by norm_num) (by linarith)
      have h2 : t / (1 - 1 / 250 : ℝ) = (250 / 249 : ℝ) * t := by ring
      linarith
    have hlq : -(q / (1 - q)) ≤ Real.log (1 - q) := hlog_one_sub q hq0.le hq1
    have hq_max : q ≤ 1285 / 1000 * (1 / 250) := by linarith
    have hlq2 : -(1292 / 1000 : ℝ) * t ≤ -(q / (1 - q)) := by
      have h1 : q / (1 - q) ≤ ((1285 / 1000) * t) / (1 - 1285 / 1000 * (1 / 250)) :=
        div_le_div₀ (by positivity) hq_ub (by norm_num) (by linarith)
      have h2 : ((1285 / 1000 : ℝ) * t) / (1 - 1285 / 1000 * (1 / 250)) =
          (1285 / 1000 / (1 - 1285 / 1000 * (1 / 250)) : ℝ) * t := by ring
      have h3 : (1285 / 1000 / (1 - 1285 / 1000 * (1 / 250)) : ℝ) ≤ 1292 / 1000 := by norm_num
      nlinarith
    have hdiv : -(1292 / 1000 : ℝ) * t / (1 - 1 / 250) ≤ (1 / (1 - m)) * Real.log (1 - q) := by
      have h1 : (1 / (1 - m)) * (-(1292 / 1000 : ℝ) * t) ≤ (1 / (1 - m)) * Real.log (1 - q) :=
        mul_le_mul_of_nonneg_left (hlq2.trans hlq) (by positivity)
      have h2 : -(1292 / 1000 : ℝ) * t / (1 - 1 / 250) ≤ (1 / (1 - m)) * (-(1292 / 1000 : ℝ) * t) := by
        have hinv : 1 / (1 - m) ≤ 1 / (1 - 1 / 250) := one_div_le_one_div_of_le (by norm_num) (by linarith)
        have hneg : -(1292 / 1000 : ℝ) * t ≤ 0 := by linarith
        have := mul_le_mul_of_nonpos_right hinv hneg
        linarith [show 1 / (1 - 1 / 250 : ℝ) * (-(1292 / 1000) * t) = -(1292 / 1000) * t / (1 - 1 / 250) by ring]
      exact h2.trans h1
    have hsum_coef : -(2302 / 1000 : ℝ) * t ≤ -(250 / 249 : ℝ) * t + -(1292 / 1000 : ℝ) * t / (1 - 1 / 250) := by
      have h1 : -(1292 / 1000 : ℝ) * t / (1 - 1 / 250) = -(1292 / 1000 / (1 - 1 / 250) : ℝ) * t := by ring
      have h2 : -(2302 / 1000 : ℝ) ≤ -(250 / 249 : ℝ) + -(1292 / 1000 / (1 - 1 / 250) : ℝ) := by norm_num
      nlinarith
    linarith
  -- Step 5: Lower bound log m ≥ log t - t ≥ log t - 1/250
  have hlogm_lb : Real.log t - 1 / 250 ≤ Real.log m := by
    have h1 := Real.log_le_log (mul_pos ht0 (Real.exp_pos _)) hm_lo
    rw [Real.log_mul ht0.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  -- Step 6: Lower bound 1 - X ≥ m + q - m * q ≥ 2.264 * t, so log(1 - X) ≥ 0.817 + log t
  have h1mX_lb : (2264 / 1000 : ℝ) * t ≤ 1 - X := by
    have h1 : m + q - m * q ≤ 1 - X := by linarith
    have hm_lb2 : (1 - 1 / 250 : ℝ) * t ≤ m := by
      have he : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
      nlinarith
    have hmq_ub : m * q ≤ (1285 / 1000 * (1 / 250)) * t := by
      have : m * q ≤ (1 / 250) * ((1285 / 1000) * t) :=
        mul_le_mul (by linarith) hq_ub hq0.le (by norm_num)
      linarith
    linarith
  have hlog2264 : (817 / 1000 : ℝ) ≤ Real.log (2264 / 1000 : ℝ) := by
    have h := Real.exp_bound (x := (817 / 1000 : ℝ)) (n := 5) (by norm_num) (by norm_num)
    rw [abs_le] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have hexp : Real.exp (817 / 1000 : ℝ) ≤ 2264 / 1000 := by linarith
    calc (817 / 1000 : ℝ) = Real.log (Real.exp (817 / 1000)) := (Real.log_exp _).symm
      _ ≤ Real.log (2264 / 1000) := Real.log_le_log (Real.exp_pos _) hexp
  have hlog1mX_lb : (817 / 1000 : ℝ) + Real.log t ≤ Real.log (1 - X) := by
    have h1 := Real.log_le_log (by positivity) h1mX_lb
    rw [Real.log_mul (by norm_num) ht0.ne'] at h1
    linarith
  -- Step 7: Sum everything!
  -- 2 * (3/4 t - t log t) + (-2.302 t) + t * (log t - 0.004) + t * (0.817 + log t)
  -- = (1.500 - 2.302 - 0.004 + 0.817) * t = +0.011 * t > 0!
  nlinarith [mul_le_mul_of_nonneg_left hlogm_lb ht0.le,
             mul_le_mul_of_nonneg_left hlog1mX_lb ht0.le]

/-- For `b = 2/25` and `t ∈ (0, 1]`, `0 < F_{0.08}(t) - t * F'_{0.08}(t)` (so `B(t) < 1`). -/
lemma FFn_008_B_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < FFn (2 / 25) t - t * FFn' (2 / 25) t := by
  have heq : FFn (2 / 25) t - t * FFn' (2 / 25) t =
      Real.log (1 + t) + t ^ 2 * (-(33 / 100 : ℝ) - (2 / 25) * t + (2 / 25) * t ^ 2) * Real.exp (-t) := by
    unfold FFn FFn' hEntN gFn gFn'
    ring
  rw [heq]
  have h1t : 0 < 1 + t := by linarith
  have hlog_lb : t / (1 + t) ≤ Real.log (1 + t) := by
    have h := Real.one_sub_inv_le_log_of_pos h1t
    have h2 : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [h1t.ne']; ring
    rwa [h2] at h
  have hexp_ub : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ h1t (by linarith [Real.add_one_le_exp t])
  have hpoly : -(41 / 100 : ℝ) ≤ -(33 / 100 : ℝ) - (2 / 25) * t + (2 / 25) * t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hterm : -(41 / 100 : ℝ) * (t / (1 + t)) ≤
      t ^ 2 * (-(33 / 100 : ℝ) - (2 / 25) * t + (2 / 25) * t ^ 2) * Real.exp (-t) := by
    have h1 : t ^ 2 * (-(41 / 100 : ℝ)) * Real.exp (-t) ≤
        t ^ 2 * (-(33 / 100 : ℝ) - (2 / 25) * t + (2 / 25) * t ^ 2) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (sq_nonneg t)) (Real.exp_pos _).le
    have h2 : t ^ 2 * Real.exp (-t) ≤ t / (1 + t) := by
      have ht_le : t ^ 2 ≤ t := by nlinarith
      calc t ^ 2 * Real.exp (-t) ≤ t * (1 / (1 + t)) :=
            mul_le_mul ht_le hexp_ub (Real.exp_pos _).le ht0.le
        _ = t / (1 + t) := by ring
    nlinarith
  have hpos_frac : 0 < t / (1 + t) := div_pos ht0 h1t
  linarith

/-- For `b = 2/25` and `t ∈ (0, 1]`, `F_{0.08}(t) ≤ (1 + t) * F'_{0.08}(t)` (so `A(t) ≤ B(t)`). -/
lemma FFn_008_AB_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    FFn (2 / 25) t ≤ (1 + t) * FFn' (2 / 25) t := by
  let D : ℝ → ℝ := fun s => (1 + s) * FFn' (2 / 25) s - FFn (2 / 25) s
  have hD_deriv : ∀ s ∈ Ioc (0 : ℝ) 1, HasDerivAt D ((1 + s) * FFn'' (2 / 25) s) s := by
    intro s hs
    have hd1 : HasDerivAt (fun u : ℝ => 1 + u) 1 s :=
      ((hasDerivAt_const s (1 : ℝ)).fun_add (hasDerivAt_id s)).congr_deriv (by norm_num)
    have hd2 : HasDerivAt (fun u : ℝ => FFn' (2 / 25) u) (FFn'' (2 / 25) s) s :=
      hasDerivAt_FFn' (2 / 25) hs.1
    have hd3 : HasDerivAt (fun u : ℝ => FFn (2 / 25) u) (FFn' (2 / 25) s) s :=
      hasDerivAt_FFn (2 / 25) hs.1
    exact ((hd1.fun_mul hd2).fun_sub hd3).congr_deriv (by ring)
  have hD_anti : AntitoneOn D (Ioc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · intro s hs; exact (hD_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs; exact (hD_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have h := interior_subset hs
      rw [(hD_deriv s h).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith [h.1])
        (FFn''_neg (by norm_num) (by norm_num) h.1 h.2).le
  have hD1_le : D 1 ≤ D t := hD_anti ⟨ht0, ht1⟩ ⟨zero_lt_one, le_rfl⟩ ht1
  have hD1_pos : 0 ≤ D 1 := by
    dsimp [D]
    unfold FFn FFn' hEntN gFn gFn'
    rw [Real.log_one]
    have heq : (1 + (1 : ℝ)) * (Real.log (1 + 1) - 0 +
          (-(1 / 4) + (2 * (2 / 25) + 1 / 4) * 1 + (6 / 25 - 2 / 25) * 1 ^ 2 - (2 / 25) * 1 ^ 3) *
            Real.exp (-1)) -
        ((1 + 1) * Real.log (1 + 1) - 1 * 0 +
          (-(1 / 4) * 1 + (2 / 25) * 1 ^ 2 + (2 / 25) * 1 ^ 3) * Real.exp (-1)) =
        (57 / 100 : ℝ) * Real.exp (-1) := by ring
    rw [heq]
    positivity
  dsimp [D] at hD1_le
  linarith

end Erdos627AFM

/- ==================== Section: NumericsCert.lean ====================-/
namespace Erdos627AFM

open Real Set

/- ### Extra interval arithmetic helpers and MVT bound -/

def Iv.expOk (I : Iv) : Bool :=
  decide (|I.lo| ≤ 8 * ivScale ∧ |I.hi| ≤ 8 * ivScale)

lemma Iv.mem_exp_of_ok {I : Iv} {x : ℝ} (hok : I.expOk = true) (hx : I.Mem x) :
    (I.exp).Mem (Real.exp x) := by
  unfold Iv.expOk at hok
  rw [decide_eq_true_eq] at hok
  exact Iv.mem_exp hok.1 hok.2 hx

def Iv.maxAbs (I : Iv) : ℤ := max |I.lo| |I.hi|

lemma Iv.maxAbs_nonneg (I : Iv) : 0 ≤ I.maxAbs :=
  le_trans (abs_nonneg I.lo) (le_max_left _ _)

lemma Iv.abs_le_maxAbs {I : Iv} {x : ℝ} (hx : I.Mem x) :
    |x| ≤ (I.maxAbs : ℝ) / (ivScale : ℝ) := by
  have hD := ivScale_pos
  have hlo : -((I.maxAbs : ℝ) / (ivScale : ℝ)) ≤ (I.lo : ℝ) / (ivScale : ℝ) := by
    rw [← neg_div]
    apply div_le_div_of_nonneg_right _ hD.le
    have h1 : -|I.lo| ≤ I.lo := neg_abs_le I.lo
    have h2 : |I.lo| ≤ I.maxAbs := le_max_left _ _
    have h3 : -I.maxAbs ≤ I.lo := by linarith
    exact_mod_cast h3
  have hhi : (I.hi : ℝ) / (ivScale : ℝ) ≤ (I.maxAbs : ℝ) / (ivScale : ℝ) := by
    apply div_le_div_of_nonneg_right _ hD.le
    have h1 : I.hi ≤ |I.hi| := le_abs_self I.hi
    have h2 : |I.hi| ≤ I.maxAbs := le_max_right _ _
    have h3 : I.hi ≤ I.maxAbs := by linarith
    exact_mod_cast h3
  exact abs_le.2 ⟨hlo.trans hx.1, hx.2.trans hhi⟩

def mvtBound (Vm Vd : Iv) (lo hi : ℤ) : Iv :=
  let m := (lo + hi) / 2
  let rad := max (hi - m) (m - lo)
  let err := divHi (Vd.maxAbs * rad) ivScale
  ⟨Vm.lo - err, Vm.hi + err⟩

lemma mem_mvtBound {f f' : ℝ → ℝ} {Vm Vd : Iv} {lo hi : ℤ}
    (hle : lo ≤ hi)
    (hm_mem : Vm.Mem (f (((lo + hi) / 2 : ℤ) / (ivScale : ℝ))))
    (hderiv : ∀ t ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      HasDerivAt f (f' t) t ∧ Vd.Mem (f' t))
    {t : ℝ} (ht : t ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ))) :
    (mvtBound Vm Vd lo hi).Mem (f t) := by
  have hD := ivScale_pos
  have hDi := ivScale_pos_int
  set m : ℤ := (lo + hi) / 2
  set rad : ℤ := max (hi - m) (m - lo)
  set err : ℤ := divHi (Vd.maxAbs * rad) ivScale
  have hm_ge : lo ≤ m := by dsimp [m]; omega
  have hm_le : m ≤ hi := by dsimp [m]; omega
  have hrad_nn : 0 ≤ rad := le_trans (by omega : 0 ≤ hi - m) (le_max_left _ _)
  have hmr : ((m : ℝ) / (ivScale : ℝ)) ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)) :=
    ⟨div_le_div_of_nonneg_right (by exact_mod_cast hm_ge) hD.le,
     div_le_div_of_nonneg_right (by exact_mod_cast hm_le) hD.le⟩
  have hdist : |t - (m : ℝ) / (ivScale : ℝ)| ≤ (rad : ℝ) / (ivScale : ℝ) := by
    rw [abs_le]
    have h1 : (m : ℝ) - (lo : ℝ) ≤ (rad : ℝ) := by
      have : m - lo ≤ rad := le_max_right _ _
      exact_mod_cast this
    have h2 : (hi : ℝ) - (m : ℝ) ≤ (rad : ℝ) := by
      have : hi - m ≤ rad := le_max_left _ _
      exact_mod_cast this
    constructor
    · have : -((rad : ℝ) / (ivScale : ℝ)) ≤ ((lo : ℝ) - (m : ℝ)) / (ivScale : ℝ) := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hD.le
      rw [sub_div] at this
      linarith [ht.1]
    · have : ((hi : ℝ) - (m : ℝ)) / (ivScale : ℝ) ≤ (rad : ℝ) / (ivScale : ℝ) :=
        div_le_div_of_nonneg_right h2 hD.le
      rw [sub_div] at this
      linarith [ht.2]
  have hdiff : |f t - f ((m : ℝ) / (ivScale : ℝ))| ≤ (err : ℝ) / (ivScale : ℝ) := by
    have hprod_le : ((Vd.maxAbs : ℝ) / (ivScale : ℝ)) * ((rad : ℝ) / (ivScale : ℝ)) ≤
        (err : ℝ) / (ivScale : ℝ) := by
      have h1 := le_divHi (Vd.maxAbs * rad) ivScale hDi
      have h2 : (Vd.maxAbs : ℝ) * (rad : ℝ) / (ivScale : ℝ) ≤ (err : ℝ) := by
        simpa [err] using h1
      have h3 := div_le_div_of_nonneg_right h2 hD.le
      linarith [show ((Vd.maxAbs : ℝ) / (ivScale : ℝ)) * ((rad : ℝ) / (ivScale : ℝ)) =
        (Vd.maxAbs : ℝ) * (rad : ℝ) / (ivScale : ℝ) / (ivScale : ℝ) by ring]
    have hVd_nn : 0 ≤ (Vd.maxAbs : ℝ) / (ivScale : ℝ) :=
      div_nonneg (by exact_mod_cast Vd.maxAbs_nonneg) hD.le
    rcases lt_trichotomy t ((m : ℝ) / (ivScale : ℝ)) with hlt | heq | hgt
    · have hsub : Icc t ((m : ℝ) / (ivScale : ℝ)) ⊆ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)) :=
        Icc_subset_Icc ht.1 hmr.2
      have hcont : ContinuousOn f (Icc t ((m : ℝ) / (ivScale : ℝ))) := fun u hu =>
        (hderiv u (hsub hu)).1.continuousAt.continuousWithinAt
      have hd : ∀ u ∈ Ioo t ((m : ℝ) / (ivScale : ℝ)), HasDerivAt f (f' u) u := fun u hu =>
        (hderiv u (hsub ⟨hu.1.le, hu.2.le⟩)).1
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hd
      have hfc := Iv.abs_le_maxAbs (hderiv c (hsub ⟨hc.1.le, hc.2.le⟩)).2
      have hfeq : f t - f ((m : ℝ) / (ivScale : ℝ)) = f' c * (t - (m : ℝ) / (ivScale : ℝ)) := by
        have hne : (m : ℝ) / (ivScale : ℝ) - t ≠ 0 := (sub_pos.2 hlt).ne'
        have := (eq_div_iff hne).1 hceq
        linarith
      rw [hfeq, abs_mul]
      exact (mul_le_mul hfc hdist (abs_nonneg _) hVd_nn).trans hprod_le
    · rw [heq, sub_self, abs_zero]
      exact (mul_nonneg hVd_nn
        (div_nonneg (by exact_mod_cast hrad_nn) hD.le)).trans hprod_le
    · have hsub : Icc ((m : ℝ) / (ivScale : ℝ)) t ⊆ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)) :=
        Icc_subset_Icc hmr.1 ht.2
      have hcont : ContinuousOn f (Icc ((m : ℝ) / (ivScale : ℝ)) t) := fun u hu =>
        (hderiv u (hsub hu)).1.continuousAt.continuousWithinAt
      have hd : ∀ u ∈ Ioo ((m : ℝ) / (ivScale : ℝ)) t, HasDerivAt f (f' u) u := fun u hu =>
        (hderiv u (hsub ⟨hu.1.le, hu.2.le⟩)).1
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f f' hgt hcont hd
      have hfc := Iv.abs_le_maxAbs (hderiv c (hsub ⟨hc.1.le, hc.2.le⟩)).2
      have hfeq : f t - f ((m : ℝ) / (ivScale : ℝ)) = f' c * (t - (m : ℝ) / (ivScale : ℝ)) := by
        have hne : t - (m : ℝ) / (ivScale : ℝ) ≠ 0 := (sub_pos.2 hgt).ne'
        have := (eq_div_iff hne).1 hceq
        linarith
      rw [hfeq, abs_mul]
      exact (mul_le_mul hfc hdist (abs_nonneg _) hVd_nn).trans hprod_le
  rw [abs_le] at hdiff
  refine ⟨?_, ?_⟩
  · simp only [mvtBound, Int.cast_sub, sub_div]
    linarith [hm_mem.1, hdiff.1]
  · simp only [mvtBound, Int.cast_add, add_div]
    linarith [hm_mem.2, hdiff.2]

/- ### Real derivative lemmas for log X and the Phi functions -/

noncomputable def logXFn (b : ℝ) (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (1 - M t) + Real.log (1 - Real.exp (-FFn' b t)) / (1 - M t)

noncomputable def logXFn' (b : ℝ) (M M' : ℝ → ℝ) (t : ℝ) : ℝ :=
  let P := 1 - Real.exp (-FFn' b t)
  (M' t / (1 - M t)) * (Real.log P / (1 - M t) - 1) +
    (FFn'' b t / (1 - M t)) * (Real.exp (-FFn' b t) / P)

lemma log_X_eq_logXFn {b : ℝ} {M : ℝ → ℝ} {t : ℝ}
    (hM1 : M t < 1) (hFp : 0 < FFn' b t) :
    Real.log ((1 - Real.exp (-FFn' b t)) ^ (1 / (1 - M t)) * (1 - M t)) = logXFn b M t := by
  have h1M : 0 < 1 - M t := sub_pos.2 hM1
  have hP : 0 < 1 - Real.exp (-FFn' b t) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  unfold logXFn
  rw [Real.log_mul (Real.rpow_pos_of_pos hP _).ne' h1M.ne', Real.log_rpow hP]
  ring

lemma hasDerivAt_logXFn {b : ℝ} {M M' : ℝ → ℝ} {t : ℝ}
    (ht0 : 0 < t) (hM : HasDerivAt M (M' t) t) (hM1 : M t < 1) (hFp : 0 < FFn' b t) :
    HasDerivAt (logXFn b M) (logXFn' b M M' t) t := by
  have h1M : 0 < 1 - M t := sub_pos.2 hM1
  have hP : 0 < 1 - Real.exp (-FFn' b t) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  have hd_1M : HasDerivAt (fun s => 1 - M s) (-M' t) t :=
    ((hasDerivAt_const t (1 : ℝ)).fun_sub hM).congr_deriv (by ring)
  have hd_log1M : HasDerivAt (fun s => Real.log (1 - M s)) (-M' t / (1 - M t)) t :=
    hd_1M.log h1M.ne'
  have hd_q : HasDerivAt (fun s => Real.exp (-FFn' b s))
      (Real.exp (-FFn' b t) * (-FFn'' b t)) t :=
    (hasDerivAt_FFn' b ht0).fun_neg.exp
  have hd_P : HasDerivAt (fun s => 1 - Real.exp (-FFn' b s))
      (Real.exp (-FFn' b t) * FFn'' b t) t :=
    ((hasDerivAt_const t (1 : ℝ)).fun_sub hd_q).congr_deriv (by ring)
  have hd_logP : HasDerivAt (fun s => Real.log (1 - Real.exp (-FFn' b s)))
      (Real.exp (-FFn' b t) * FFn'' b t / (1 - Real.exp (-FFn' b t))) t :=
    hd_P.log hP.ne'
  have hd_div := hd_logP.fun_div hd_1M h1M.ne'
  refine (hd_log1M.fun_add hd_div).congr_deriv ?_
  unfold logXFn'
  field_simp [h1M.ne', hP.ne']
  ring

lemma M0_t_mul_deriv_div {t : ℝ} (ht0 : 0 < t) :
    t * M0Fn' t / M0Fn t = 1 - t := by
  unfold M0Fn M0Fn'
  field_simp [ht0.ne', (Real.exp_pos (-t)).ne']

lemma M1_t_mul_deriv_div {t : ℝ} (ht0 : 0 < t) :
    t * M1Fn' t / M1Fn t = 1 - (2 / 3) * t - (3 / 5) * t ^ 2 := by
  unfold M1Fn M1Fn'
  field_simp [ht0.ne', (Real.exp_pos _).ne']

lemma hasDerivAt_baseFn {b : ℝ} {M M' : ℝ → ℝ} {t : ℝ}
    (ht0 : 0 < t) (hM : HasDerivAt M (M' t) t) (hM0 : 0 < M t) (hM1 : M t < 1) (hFp : 0 < FFn' b t) :
    HasDerivAt (fun s => 2 * FFn b s + logXFn b M s + s * Real.log (M s))
      (2 * FFn' b t + logXFn' b M M' t + Real.log (M t) + t * M' t / M t) t := by
  have hdF : HasDerivAt (fun s => 2 * FFn b s) (2 * FFn' b t) t :=
    (hasDerivAt_FFn b ht0).const_mul 2
  have hdX := hasDerivAt_logXFn ht0 hM hM1 hFp
  have hdM : HasDerivAt (fun s => s * Real.log (M s)) (Real.log (M t) + t * M' t / M t) t := by
    have hlogM := hM.log hM0.ne'
    refine ((hasDerivAt_id t).fun_mul hlogM).congr_deriv ?_
    simp only [id_eq]; ring
  exact ((hdF.fun_add hdX).fun_add hdM).congr_deriv (by ring)

lemma hasDerivAt_ESFn {b : ℝ} {M M' : ℝ → ℝ} {t : ℝ}
    (ht0 : 0 < t) (hM : HasDerivAt M (M' t) t) (hM0 : 0 < M t) (hM1 : M t < 1)
    (hFp : 0 < FFn' b t) (hX1 : Real.exp (logXFn b M t) < 1) :
    HasDerivAt (fun s => 2 * FFn b s + logXFn b M s + s * Real.log (M s) +
        s * Real.log (1 - Real.exp (logXFn b M s)))
      (2 * FFn' b t + logXFn' b M M' t + Real.log (M t) + t * M' t / M t +
        Real.log (1 - Real.exp (logXFn b M t)) -
        t * (Real.exp (logXFn b M t) / (1 - Real.exp (logXFn b M t))) * logXFn' b M M' t) t := by
  have hdBase := hasDerivAt_baseFn ht0 hM hM0 hM1 hFp
  have h1X : 0 < 1 - Real.exp (logXFn b M t) := sub_pos.2 hX1
  have hd_expX : HasDerivAt (fun s => Real.exp (logXFn b M s))
      (Real.exp (logXFn b M t) * logXFn' b M M' t) t :=
    (hasDerivAt_logXFn ht0 hM hM1 hFp).exp
  have hd_1mX : HasDerivAt (fun s => 1 - Real.exp (logXFn b M s))
      (-(Real.exp (logXFn b M t) * logXFn' b M M' t)) t :=
    ((hasDerivAt_const t (1 : ℝ)).fun_sub hd_expX).congr_deriv (by ring)
  have hd_log1mX : HasDerivAt (fun s => Real.log (1 - Real.exp (logXFn b M s)))
      (-(Real.exp (logXFn b M t) * logXFn' b M M' t) / (1 - Real.exp (logXFn b M t))) t :=
    hd_1mX.log h1X.ne'
  have hd_term := (hasDerivAt_id t).fun_mul hd_log1mX
  refine (hdBase.fun_add hd_term).congr_deriv ?_
  simp only [id_eq]; ring

lemma hasDerivAt_MidFn {b : ℝ} {M M' : ℝ → ℝ} {c t : ℝ}
    (ht0 : 0 < t) (hM : HasDerivAt M (M' t) t) (hM0 : 0 < M t) (hM1 : M t < 1) (hFp : 0 < FFn' b t) :
    HasDerivAt (fun s => 2 * FFn b s + (1 - s) * logXFn b M s + s * (Real.log (M s) - c))
      (2 * FFn' b t + (1 - t) * logXFn' b M M' t - logXFn b M t + Real.log (M t) + t * M' t / M t - c) t := by
  have hdF : HasDerivAt (fun s => 2 * FFn b s) (2 * FFn' b t) t :=
    (hasDerivAt_FFn b ht0).const_mul 2
  have hd1ms : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
    ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).congr_deriv (by norm_num)
  have hdX := hasDerivAt_logXFn ht0 hM hM1 hFp
  have hd1 := hd1ms.fun_mul hdX
  have hdM : HasDerivAt (fun s => s * (Real.log (M s) - c))
      (Real.log (M t) - c + t * M' t / M t) t := by
    have hlogM := (hM.log hM0.ne').fun_sub (hasDerivAt_const t c)
    refine ((hasDerivAt_id t).fun_mul hlogM).congr_deriv ?_
    simp only [id_eq]; ring
  exact ((hdF.fun_add hd1).fun_add hdM).congr_deriv (by ring)

lemma hasDerivAt_constYFn {b : ℝ} {M M' : ℝ → ℝ} {c t : ℝ}
    (ht0 : 0 < t) (hM : HasDerivAt M (M' t) t) (hM0 : 0 < M t) (hM1 : M t < 1) (hFp : 0 < FFn' b t) :
    HasDerivAt (fun s => 2 * FFn b s + logXFn b M s + s * Real.log (M s) + s * c)
      (2 * FFn' b t + logXFn' b M M' t + Real.log (M t) + t * M' t / M t + c) t := by
  have hdBase := hasDerivAt_baseFn ht0 hM hM0 hM1 hFp
  have hdC : HasDerivAt (fun s : ℝ => s * c) c t := by
    simpa using (hasDerivAt_id t).mul_const c
  exact hdBase.fun_add hdC

/- ### Computable interval evaluators for F_b, F'_b, F''_b, M_0, M_1 -/

def ivF_pt (bn bd a : ℤ) : Iv :=
  let one := Iv.ofInt 1
  let T := Iv.ofScaled a
  let T2 := T.sqNonneg
  let T3 := T2.mul T
  let ent := (one.add T).mul (Iv.logPt (ivScale + a)) |>.sub (T.mul (Iv.logPt a))
  let poly := ((Iv.ofRat (-1) 4).mul T).add ((Iv.ofRat bn bd).mul T2) |>.add ((Iv.ofRat 2 25).mul T3)
  ent.add (poly.mul (Iv.expPt (-a)))

def ivFp_pt (bn bd a : ℤ) : Iv :=
  let T := Iv.ofScaled a
  let T2 := T.sqNonneg
  let T3 := T2.mul T
  let entp := (Iv.logPt (ivScale + a)).sub (Iv.logPt a)
  let c1 := (Iv.ofRat (2 * bn) bd).add (Iv.ofRat 1 4)
  let c2 := (Iv.ofRat 6 25).sub (Iv.ofRat bn bd)
  let poly := (((Iv.ofRat (-1) 4).add (c1.mul T)).add (c2.mul T2)).sub ((Iv.ofRat 2 25).mul T3)
  entp.add (poly.mul (Iv.expPt (-a)))

def ivFpp_iv (bn bd : ℤ) (T : Iv) : Iv :=
  let one := Iv.ofInt 1
  let T2 := T.sqNonneg
  let T3 := T2.mul T
  let t1 := (one.divPos (T.mul (one.add T))).neg
  let c0 := (Iv.ofRat 1 2).add (Iv.ofRat (2 * bn) bd)
  let c1 := (Iv.ofRat 23 100).sub (Iv.ofRat (4 * bn) bd)
  let c2 := (Iv.ofRat bn bd).sub (Iv.ofRat 12 25)
  let poly := ((c0.add (c1.mul T)).add (c2.mul T2)).add ((Iv.ofRat 2 25).mul T3)
  t1.add (poly.mul (Iv.exp T.neg))

def ivM0_pt (a : ℤ) : Iv := (Iv.ofScaled a).mul (Iv.expPt (-a))

def ivM0_iv (lo hi : ℤ) : Iv := ⟨(ivM0_pt lo).lo, (ivM0_pt hi).hi⟩

def ivM0p_iv (T : Iv) : Iv := ((Iv.ofInt 1).sub T).mul (Iv.exp T.neg)

def ivM1_pt (a : ℤ) : Iv :=
  let T := Iv.ofScaled a
  let T2 := T.sqNonneg
  let expo := ((Iv.ofRat (-2) 3).mul T).sub ((Iv.ofRat 3 10).mul T2)
  T.mul (Iv.exp expo)

def ivM1_iv (T : Iv) : Iv :=
  let T2 := T.sqNonneg
  let expo := ((Iv.ofRat (-2) 3).mul T).sub ((Iv.ofRat 3 10).mul T2)
  T.mul (Iv.exp expo)

def ivM1p_iv (T : Iv) : Iv :=
  let T2 := T.sqNonneg
  let expo := ((Iv.ofRat (-2) 3).mul T).sub ((Iv.ofRat 3 10).mul T2)
  (((Iv.ofInt 1).sub ((Iv.ofRat 2 3).mul T)).sub ((Iv.ofRat 3 5).mul T2)).mul (Iv.exp expo)

/- ### Soundness of the basic interval evaluators -/

lemma mem_ofScaled (a : ℤ) : (Iv.ofScaled a).Mem ((a : ℝ) / (ivScale : ℝ)) := ⟨le_rfl, le_rfl⟩

lemma mem_ivF_pt {bn bd a : ℤ} (hbd : 0 < bd) (ha0 : 0 < a) (ha1 : a ≤ ivScale)
    (hok1 : Iv.logPtOk a = true) (hok2 : Iv.logPtOk (ivScale + a) = true) :
    (ivF_pt bn bd a).Mem (FFn ((bn : ℝ) / (bd : ℝ)) ((a : ℝ) / (ivScale : ℝ))) := by
  have hD := ivScale_pos
  have hT : (Iv.ofScaled a).Mem ((a : ℝ) / (ivScale : ℝ)) := mem_ofScaled a
  have hT2 : (Iv.ofScaled a).sqNonneg.Mem (((a : ℝ) / (ivScale : ℝ)) ^ 2) := by
    rw [sq]; exact Iv.mem_sqNonneg (show 0 ≤ (Iv.ofScaled a).lo by dsimp [Iv.ofScaled]; omega) hT
  have hT3 : ((Iv.ofScaled a).sqNonneg.mul (Iv.ofScaled a)).Mem (((a : ℝ) / (ivScale : ℝ)) ^ 3) := by
    rw [pow_succ]; exact Iv.mem_mul hT2 hT
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have h1T : ((Iv.ofInt 1).add (Iv.ofScaled a)).Mem (1 + (a : ℝ) / (ivScale : ℝ)) :=
    Iv.mem_add h1 hT
  have hlog1T : (Iv.logPt (ivScale + a)).Mem (Real.log (1 + (a : ℝ) / (ivScale : ℝ))) := by
    have heq : ((ivScale + a : ℤ) : ℝ) / (ivScale : ℝ) = 1 + (a : ℝ) / (ivScale : ℝ) := by
      push_cast; field_simp [hD.ne']
    rw [← heq]; exact Iv.mem_logPt hok2
  have hlogT := Iv.mem_logPt hok1
  have hent := Iv.mem_sub (Iv.mem_mul h1T hlog1T) (Iv.mem_mul hT hlogT)
  have hr1 : (Iv.ofRat (-1) 4).Mem (-(1 / 4 : ℝ)) := by
    simpa [neg_div] using Iv.mem_ofRat (p := -1) (q := 4) (by norm_num)
  have hr2 : (Iv.ofRat bn bd).Mem ((bn : ℝ) / (bd : ℝ)) := Iv.mem_ofRat hbd
  have hr3 : (Iv.ofRat 2 25).Mem ((2 : ℝ) / 25) := by
    simpa using Iv.mem_ofRat (p := 2) (q := 25) (by norm_num)
  have hpoly := Iv.mem_add (Iv.mem_add (Iv.mem_mul hr1 hT) (Iv.mem_mul hr2 hT2)) (Iv.mem_mul hr3 hT3)
  have hexp : (Iv.expPt (-a)).Mem (Real.exp (-((a : ℝ) / (ivScale : ℝ)))) := by
    have heq : ((-a : ℤ) : ℝ) / (ivScale : ℝ) = -((a : ℝ) / (ivScale : ℝ)) := by push_cast; ring
    rw [← heq]
    apply Iv.mem_expPt
    have : 0 < ivScale := ivScale_pos_int
    rw [abs_neg, abs_of_pos ha0]; omega
  unfold ivF_pt FFn hEntN gFn
  exact Iv.mem_add hent (Iv.mem_mul hpoly hexp)

lemma mem_ivFp_pt {bn bd a : ℤ} (hbd : 0 < bd) (ha0 : 0 < a) (ha1 : a ≤ ivScale)
    (hok1 : Iv.logPtOk a = true) (hok2 : Iv.logPtOk (ivScale + a) = true) :
    (ivFp_pt bn bd a).Mem (FFn' ((bn : ℝ) / (bd : ℝ)) ((a : ℝ) / (ivScale : ℝ))) := by
  have hD := ivScale_pos
  have hT : (Iv.ofScaled a).Mem ((a : ℝ) / (ivScale : ℝ)) := mem_ofScaled a
  have hT2 : (Iv.ofScaled a).sqNonneg.Mem (((a : ℝ) / (ivScale : ℝ)) ^ 2) := by
    rw [sq]; exact Iv.mem_sqNonneg (show 0 ≤ (Iv.ofScaled a).lo by dsimp [Iv.ofScaled]; omega) hT
  have hT3 : ((Iv.ofScaled a).sqNonneg.mul (Iv.ofScaled a)).Mem (((a : ℝ) / (ivScale : ℝ)) ^ 3) := by
    rw [pow_succ]; exact Iv.mem_mul hT2 hT
  have hlog1T : (Iv.logPt (ivScale + a)).Mem (Real.log (1 + (a : ℝ) / (ivScale : ℝ))) := by
    have heq : ((ivScale + a : ℤ) : ℝ) / (ivScale : ℝ) = 1 + (a : ℝ) / (ivScale : ℝ) := by
      push_cast; field_simp [hD.ne']
    rw [← heq]; exact Iv.mem_logPt hok2
  have hlogT := Iv.mem_logPt hok1
  have hentp := Iv.mem_sub hlog1T hlogT
  have hr0 : (Iv.ofRat (-1) 4).Mem (-(1 / 4 : ℝ)) := by
    simpa [neg_div] using Iv.mem_ofRat (p := -1) (q := 4) (by norm_num)
  have hc1 : ((Iv.ofRat (2 * bn) bd).add (Iv.ofRat 1 4)).Mem (2 * ((bn : ℝ) / (bd : ℝ)) + 1 / 4) := by
    have h1 : (Iv.ofRat (2 * bn) bd).Mem (2 * ((bn : ℝ) / (bd : ℝ))) := by
      have := Iv.mem_ofRat (p := 2 * bn) (q := bd) hbd
      push_cast at this; simpa [mul_div_assoc] using this
    exact Iv.mem_add h1 (by simpa using Iv.mem_ofRat (p := 1) (q := 4) (by norm_num))
  have hc2 : ((Iv.ofRat 6 25).sub (Iv.ofRat bn bd)).Mem (6 / 25 - (bn : ℝ) / (bd : ℝ)) :=
    Iv.mem_sub (by simpa using Iv.mem_ofRat (p := 6) (q := 25) (by norm_num)) (Iv.mem_ofRat hbd)
  have hr3 : (Iv.ofRat 2 25).Mem ((2 : ℝ) / 25) := by
    simpa using Iv.mem_ofRat (p := 2) (q := 25) (by norm_num)
  have hpoly := Iv.mem_sub (Iv.mem_add (Iv.mem_add hr0 (Iv.mem_mul hc1 hT)) (Iv.mem_mul hc2 hT2))
    (Iv.mem_mul hr3 hT3)
  have hexp : (Iv.expPt (-a)).Mem (Real.exp (-((a : ℝ) / (ivScale : ℝ)))) := by
    have heq : ((-a : ℤ) : ℝ) / (ivScale : ℝ) = -((a : ℝ) / (ivScale : ℝ)) := by push_cast; ring
    rw [← heq]
    apply Iv.mem_expPt
    have : 0 < ivScale := ivScale_pos_int
    rw [abs_neg, abs_of_pos ha0]; omega
  unfold ivFp_pt FFn' gFn'
  exact Iv.mem_add hentp (Iv.mem_mul hpoly hexp)

lemma mem_ivFpp_iv {bn bd : ℤ} (hbd : 0 < bd) {T : Iv} {t : ℝ}
    (hTlo : 0 < T.lo) (hThi : T.hi ≤ ivScale) (ht : T.Mem t) :
    (ivFpp_iv bn bd T).Mem (FFn'' ((bn : ℝ) / (bd : ℝ)) t) := by
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have hT2 : T.sqNonneg.Mem (t ^ 2) := by rw [sq]; exact Iv.mem_sqNonneg (by omega) ht
  have hT3 : (T.sqNonneg.mul T).Mem (t ^ 3) := by rw [pow_succ]; exact Iv.mem_mul hT2 ht
  have h1T : ((Iv.ofInt 1).add T).Mem (1 + t) := Iv.mem_add h1 ht
  have hprod : (T.mul ((Iv.ofInt 1).add T)).Mem (t * (1 + t)) := Iv.mem_mul ht h1T
  have hprod_lo : 0 < (T.mul ((Iv.ofInt 1).add T)).lo := by
    have hD := ivScale_pos_int
    have hTlo_le_hi : T.lo ≤ T.hi := by
      have : (T.lo : ℝ) / (ivScale : ℝ) ≤ (T.hi : ℝ) / (ivScale : ℝ) := ht.1.trans ht.2
      have h2 := (div_le_div_iff_of_pos_right ivScale_pos).1 this
      exact_mod_cast h2
    have hpos1 : ivScale ≤ ivScale + T.lo := by omega
    have hpos2 : ivScale ≤ ivScale + T.hi := by omega
    have hlo_ge : ivScale ≤ T.lo * (ivScale + T.lo) := by
      have h1 : 1 * ivScale ≤ T.lo * (ivScale + T.lo) :=
        mul_le_mul (by omega) hpos1 (by omega) (by omega)
      linarith
    have hmin_ge : ivScale ≤ min (min (T.lo * (ivScale + T.lo)) (T.lo * (ivScale + T.hi)))
        (min (T.hi * (ivScale + T.lo)) (T.hi * (ivScale + T.hi))) := by
      refine le_min (le_min hlo_ge ?_) (le_min ?_ ?_)
      · exact hlo_ge.trans (mul_le_mul_of_nonneg_left (by omega) (by omega))
      · exact hlo_ge.trans (mul_le_mul_of_nonneg_right hTlo_le_hi (by omega))
      · exact hlo_ge.trans (mul_le_mul hTlo_le_hi (by omega) (by omega) (by omega))
    change 0 < divLo (min (min (T.lo * (1 * ivScale + T.lo)) (T.lo * (1 * ivScale + T.hi)))
        (min (T.hi * (1 * ivScale + T.lo)) (T.hi * (1 * ivScale + T.hi)))) ivScale
    simp only [one_mul, divLo]
    have hle1 : (1 : ℤ) ≤ min (min (T.lo * (ivScale + T.lo)) (T.lo * (ivScale + T.hi)))
        (min (T.hi * (ivScale + T.lo)) (T.hi * (ivScale + T.hi))) / ivScale :=
      Int.le_ediv_of_mul_le hD (by linarith)
    omega
  have ht1 : (((Iv.ofInt 1).divPos (T.mul ((Iv.ofInt 1).add T))).neg).Mem (-(1 / (t * (1 + t)))) :=
    Iv.mem_neg (Iv.mem_divPos h1 hprod_lo hprod)
  have hc0 : ((Iv.ofRat 1 2).add (Iv.ofRat (2 * bn) bd)).Mem (1 / 2 + 2 * ((bn : ℝ) / (bd : ℝ))) := by
    have h2b : (Iv.ofRat (2 * bn) bd).Mem (2 * ((bn : ℝ) / (bd : ℝ))) := by
      have := Iv.mem_ofRat (p := 2 * bn) (q := bd) hbd
      push_cast at this; simpa [mul_div_assoc] using this
    exact Iv.mem_add (by simpa using Iv.mem_ofRat (p := 1) (q := 2) (by norm_num)) h2b
  have hc1 : ((Iv.ofRat 23 100).sub (Iv.ofRat (4 * bn) bd)).Mem (23 / 100 - 4 * ((bn : ℝ) / (bd : ℝ))) := by
    have h4b : (Iv.ofRat (4 * bn) bd).Mem (4 * ((bn : ℝ) / (bd : ℝ))) := by
      have := Iv.mem_ofRat (p := 4 * bn) (q := bd) hbd
      push_cast at this; simpa [mul_div_assoc] using this
    exact Iv.mem_sub (by simpa using Iv.mem_ofRat (p := 23) (q := 100) (by norm_num)) h4b
  have hc2 : ((Iv.ofRat bn bd).sub (Iv.ofRat 12 25)).Mem ((bn : ℝ) / (bd : ℝ) - 12 / 25) :=
    Iv.mem_sub (Iv.mem_ofRat hbd) (by simpa using Iv.mem_ofRat (p := 12) (q := 25) (by norm_num))
  have hr3 : (Iv.ofRat 2 25).Mem ((2 : ℝ) / 25) := by
    simpa using Iv.mem_ofRat (p := 2) (q := 25) (by norm_num)
  have hpoly := Iv.mem_add (Iv.mem_add (Iv.mem_add hc0 (Iv.mem_mul hc1 ht)) (Iv.mem_mul hc2 hT2))
    (Iv.mem_mul hr3 hT3)
  have hexp : (Iv.exp T.neg).Mem (Real.exp (-t)) := by
    have hD := ivScale_pos_int
    have hTle : T.lo ≤ T.hi := by
      have : (T.lo : ℝ) / (ivScale : ℝ) ≤ (T.hi : ℝ) / (ivScale : ℝ) := ht.1.trans ht.2
      exact_mod_cast (div_le_div_iff_of_pos_right ivScale_pos).1 this
    apply Iv.mem_exp _ _ (Iv.mem_neg ht)
    · simp only [Iv.neg, abs_neg, abs_of_pos (by omega : 0 < T.hi)]; omega
    · simp only [Iv.neg, abs_neg, abs_of_pos hTlo]; omega
  unfold ivFpp_iv FFn'' gFn''
  exact Iv.mem_add ht1 (Iv.mem_mul hpoly hexp)

lemma mem_ivM0_pt {a : ℤ} (ha0 : 0 < a) (ha1 : a ≤ ivScale) :
    (ivM0_pt a).Mem (M0Fn ((a : ℝ) / (ivScale : ℝ))) := by
  have hD := ivScale_pos_int
  have hexp : (Iv.expPt (-a)).Mem (Real.exp (-((a : ℝ) / (ivScale : ℝ)))) := by
    have heq : ((-a : ℤ) : ℝ) / (ivScale : ℝ) = -((a : ℝ) / (ivScale : ℝ)) := by push_cast; ring
    rw [← heq]
    apply Iv.mem_expPt
    rw [abs_neg, abs_of_pos ha0]; omega
  unfold ivM0_pt M0Fn
  exact Iv.mem_mul (mem_ofScaled a) hexp

lemma M0Fn_mono : MonotoneOn M0Fn (Ioc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
  · intro t _; exact (hasDerivAt_M0Fn t).continuousAt.continuousWithinAt
  · intro t _; exact (hasDerivAt_M0Fn t).differentiableAt.differentiableWithinAt
  · intro t ht
    have h := interior_subset ht
    rw [(hasDerivAt_M0Fn t).deriv]
    unfold M0Fn'
    exact mul_nonneg (by linarith [h.2]) (Real.exp_pos _).le

lemma mem_ivM0_iv {lo hi : ℤ} (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi ≤ ivScale)
    {t : ℝ} (ht : (⟨lo, hi⟩ : Iv).Mem t) :
    (ivM0_iv lo hi).Mem (M0Fn t) := by
  have hD := ivScale_pos
  have h1 := mem_ivM0_pt hlo (hle.trans hhi)
  have h2 := mem_ivM0_pt (by omega : 0 < hi) hhi
  have hlo_mem : ((lo : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (by exact_mod_cast hlo) hD, (div_le_one hD).2 (by exact_mod_cast (hle.trans hhi))⟩
  have hhi_mem : ((hi : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (by exact_mod_cast (by omega : 0 < hi)) hD, (div_le_one hD).2 (by exact_mod_cast hhi)⟩
  have ht_mem : t ∈ Ioc (0 : ℝ) 1 := ⟨hlo_mem.1.trans_le ht.1, ht.2.trans hhi_mem.2⟩
  exact ⟨h1.1.trans (M0Fn_mono hlo_mem ht_mem ht.1), (M0Fn_mono ht_mem hhi_mem ht.2).trans h2.2⟩

lemma mem_ivM0p_iv {T : Iv} {t : ℝ} (hlo : 0 < T.lo) (hhi : T.hi ≤ ivScale) (ht : T.Mem t) :
    (ivM0p_iv T).Mem (M0Fn' t) := by
  have hD := ivScale_pos_int
  have hTle : T.lo ≤ T.hi := by
    have : (T.lo : ℝ) / (ivScale : ℝ) ≤ (T.hi : ℝ) / (ivScale : ℝ) := ht.1.trans ht.2
    exact_mod_cast (div_le_div_iff_of_pos_right ivScale_pos).1 this
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have hexp : (Iv.exp T.neg).Mem (Real.exp (-t)) := by
    apply Iv.mem_exp _ _ (Iv.mem_neg ht)
    · simp only [Iv.neg, abs_neg, abs_of_pos (by omega : 0 < T.hi)]; omega
    · simp only [Iv.neg, abs_neg, abs_of_pos hlo]; omega
  unfold ivM0p_iv M0Fn'
  exact Iv.mem_mul (Iv.mem_sub h1 ht) hexp

lemma mem_ivM1_expo {T : Iv} {t : ℝ} (hlo : 0 ≤ T.lo) (ht : T.Mem t) :
    (((Iv.ofRat (-2) 3).mul T).sub ((Iv.ofRat 3 10).mul T.sqNonneg)).Mem
      (-(2 / 3) * t - (3 / 10) * t ^ 2) := by
  have hT2 : T.sqNonneg.Mem (t ^ 2) := by rw [sq]; exact Iv.mem_sqNonneg hlo ht
  have hr1 : (Iv.ofRat (-2) 3).Mem (-(2 / 3 : ℝ)) := by
    simpa [neg_div] using Iv.mem_ofRat (p := -2) (q := 3) (by norm_num)
  have hr2 : (Iv.ofRat 3 10).Mem ((3 : ℝ) / 10) := by
    simpa using Iv.mem_ofRat (p := 3) (q := 10) (by norm_num)
  exact Iv.mem_sub (Iv.mem_mul hr1 ht) (Iv.mem_mul hr2 hT2)

lemma ivM1_expo_expOk {T : Iv} (hlo : 0 ≤ T.lo) (hhi : T.hi ≤ ivScale) (hle : T.lo ≤ T.hi) :
    ((((Iv.ofRat (-2) 3).mul T).sub ((Iv.ofRat 3 10).mul T.sqNonneg)).expOk) = true := by
  have hDv : ivScale = 1000000000 := rfl
  have hD := ivScale_pos_int
  have hlo' : 0 ≤ T.lo := hlo
  have hhi' : T.hi ≤ 1000000000 := by omega
  have hr1_lo : (Iv.ofRat (-2) 3).lo = -666666667 := by decide
  have hr1_hi : (Iv.ofRat (-2) 3).hi = -666666666 := by decide
  have hr2_lo : (Iv.ofRat 3 10).lo = 300000000 := by decide
  have hr2_hi : (Iv.ofRat 3 10).hi = 300000000 := by decide
  have h1_lo : -1000000000 ≤ ((Iv.ofRat (-2) 3).mul T).lo := by
    simp only [Iv.mul, hr1_lo, hr1_hi, divLo]
    have hmin : -1000000000 * ivScale ≤ min (min (-666666667 * T.lo) (-666666667 * T.hi))
        (min (-666666666 * T.lo) (-666666666 * T.hi)) := by
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> omega
    exact Int.le_ediv_of_mul_le hD hmin
  have h1_hi : ((Iv.ofRat (-2) 3).mul T).hi ≤ 1000000000 := by
    simp only [Iv.mul, hr1_lo, hr1_hi, divHi]
    have hmax : max (max (-666666667 * T.lo) (-666666667 * T.hi))
        (max (-666666666 * T.lo) (-666666666 * T.hi)) ≤ 0 := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> omega
    exact Int.ediv_le_of_le_mul hD (by omega)
  have hsq_lo : 0 ≤ T.sqNonneg.lo := by
    simp only [Iv.sqNonneg, divLo]
    exact Int.ediv_nonneg (mul_nonneg hlo hlo) hD.le
  have hsq_hi : T.sqNonneg.hi ≤ 1000000001 := by
    simp only [Iv.sqNonneg, divHi]
    have hsq : T.hi * T.hi ≤ 1000000000 * ivScale := by
      rw [hDv]; exact mul_le_mul hhi' hhi' (by omega) (by norm_num)
    exact Int.ediv_le_of_le_mul hD (by omega)
  have h2_lo : 0 ≤ ((Iv.ofRat 3 10).mul T.sqNonneg).lo := by
    simp only [Iv.mul, hr2_lo, hr2_hi, divLo]
    have hmin : 0 ≤ min (min (300000000 * T.sqNonneg.lo) (300000000 * T.sqNonneg.hi))
        (min (300000000 * T.sqNonneg.lo) (300000000 * T.sqNonneg.hi)) := by
      have hsq_le : T.sqNonneg.lo ≤ T.sqNonneg.hi := by
        simp only [Iv.sqNonneg, divLo, divHi]
        have h1 : T.lo * T.lo ≤ T.hi * T.hi := mul_le_mul hle hle hlo (by omega)
        exact Int.ediv_le_ediv hD (by omega)
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> omega
    exact Int.ediv_nonneg hmin hD.le
  have h2_hi : ((Iv.ofRat 3 10).mul T.sqNonneg).hi ≤ 1000000000 := by
    simp only [Iv.mul, hr2_lo, hr2_hi, divHi]
    have hmax : max (max (300000000 * T.sqNonneg.lo) (300000000 * T.sqNonneg.hi))
        (max (300000000 * T.sqNonneg.lo) (300000000 * T.sqNonneg.hi)) ≤ 300000000 * 1000000001 := by
      have hsq_le : T.sqNonneg.lo ≤ 1000000001 := by
        have h1 : T.lo * T.lo ≤ T.hi * T.hi := mul_le_mul hle hle hlo (by omega)
        have : T.sqNonneg.lo ≤ T.sqNonneg.hi := Int.ediv_le_ediv hD (by omega)
        omega
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> omega
    exact Int.ediv_le_of_le_mul hD (by omega)
  have h1_le_hi : ((Iv.ofRat (-2) 3).mul T).lo ≤ ((Iv.ofRat (-2) 3).mul T).hi := by
    simp only [Iv.mul, divLo, divHi]
    have hm : min (min ((Iv.ofRat (-2) 3).lo * T.lo) ((Iv.ofRat (-2) 3).lo * T.hi))
        (min ((Iv.ofRat (-2) 3).hi * T.lo) ((Iv.ofRat (-2) 3).hi * T.hi)) ≤
      max (max ((Iv.ofRat (-2) 3).lo * T.lo) ((Iv.ofRat (-2) 3).lo * T.hi))
        (max ((Iv.ofRat (-2) 3).hi * T.lo) ((Iv.ofRat (-2) 3).hi * T.hi)) :=
      (min_le_left _ _).trans ((min_le_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    exact Int.ediv_le_ediv hD (by omega)
  have h2_le_hi : ((Iv.ofRat 3 10).mul T.sqNonneg).lo ≤ ((Iv.ofRat 3 10).mul T.sqNonneg).hi := by
    simp only [Iv.mul, divLo, divHi]
    have hm : min (min ((Iv.ofRat 3 10).lo * T.sqNonneg.lo) ((Iv.ofRat 3 10).lo * T.sqNonneg.hi))
        (min ((Iv.ofRat 3 10).hi * T.sqNonneg.lo) ((Iv.ofRat 3 10).hi * T.sqNonneg.hi)) ≤
      max (max ((Iv.ofRat 3 10).lo * T.sqNonneg.lo) ((Iv.ofRat 3 10).lo * T.sqNonneg.hi))
        (max ((Iv.ofRat 3 10).hi * T.sqNonneg.lo) ((Iv.ofRat 3 10).hi * T.sqNonneg.hi)) :=
      (min_le_left _ _).trans ((min_le_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    exact Int.ediv_le_ediv hD (by omega)
  unfold Iv.expOk
  rw [decide_eq_true_eq]
  change |((Iv.ofRat (-2) 3).mul T).lo - ((Iv.ofRat 3 10).mul T.sqNonneg).hi| ≤ 8 * ivScale ∧
         |((Iv.ofRat (-2) 3).mul T).hi - ((Iv.ofRat 3 10).mul T.sqNonneg).lo| ≤ 8 * ivScale
  rw [hDv]
  constructor <;> rw [abs_le] <;> constructor <;> omega

lemma mem_ivM1_iv {T : Iv} {t : ℝ} (hlo : 0 ≤ T.lo) (hhi : T.hi ≤ ivScale) (hle : T.lo ≤ T.hi)
    (ht : T.Mem t) : (ivM1_iv T).Mem (M1Fn t) := by
  have hexpo := mem_ivM1_expo hlo ht
  have hok := ivM1_expo_expOk hlo hhi hle
  unfold ivM1_iv M1Fn
  exact Iv.mem_mul ht (Iv.mem_exp_of_ok hok hexpo)

lemma mem_ivM1_pt {a : ℤ} (ha0 : 0 ≤ a) (ha1 : a ≤ ivScale) :
    (ivM1_pt a).Mem (M1Fn ((a : ℝ) / (ivScale : ℝ))) :=
  mem_ivM1_iv (T := Iv.ofScaled a) ha0 ha1 le_rfl (mem_ofScaled a)

lemma mem_ivM1p_iv {T : Iv} {t : ℝ} (hlo : 0 ≤ T.lo) (hhi : T.hi ≤ ivScale) (hle : T.lo ≤ T.hi)
    (ht : T.Mem t) : (ivM1p_iv T).Mem (M1Fn' t) := by
  have h1 : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have hT2 : T.sqNonneg.Mem (t ^ 2) := by rw [sq]; exact Iv.mem_sqNonneg hlo ht
  have hr1 : (Iv.ofRat 2 3).Mem ((2 : ℝ) / 3) := by
    simpa using Iv.mem_ofRat (p := 2) (q := 3) (by norm_num)
  have hr2 : (Iv.ofRat 3 5).Mem ((3 : ℝ) / 5) := by
    simpa using Iv.mem_ofRat (p := 3) (q := 5) (by norm_num)
  have hpoly := Iv.mem_sub (Iv.mem_sub h1 (Iv.mem_mul hr1 ht)) (Iv.mem_mul hr2 hT2)
  have hexp := Iv.mem_exp_of_ok (ivM1_expo_expOk hlo hhi hle) (mem_ivM1_expo hlo ht)
  unfold ivM1p_iv M1Fn'
  exact Iv.mem_mul hpoly hexp

/- ### Computable check for Phi0 on [lo/D, hi/D] and its soundness proof -/

def checkPhi0Iv (lo hi : ℤ) : Bool :=
  let one := Iv.ofInt 1
  let m := (lo + hi) / 2
  let T : Iv := ⟨lo, hi⟩
  let Fm := ivF_pt 2 25 m
  let Fpm := ivFp_pt 2 25 m
  let Mm := ivM0_pt m
  let omMm := one.sub Mm
  let qm := Iv.exp Fpm.neg
  let Pm := one.sub qm
  let logPm := Iv.log Pm
  let logXm := (Iv.log omMm).add (logPm.divPos omMm)
  let Xm := Iv.exp logXm
  let omXm := one.sub Xm
  let Phi0_m := ((Iv.ofInt 2).mul Fm).add logXm |>.add
    ((Iv.ofScaled m).mul ((Iv.log Mm).add (Iv.log omXm)))
  let Fp : Iv := ⟨(ivFp_pt 2 25 hi).lo, (ivFp_pt 2 25 lo).hi⟩
  let Fpp := ivFpp_iv 2 25 T
  let M := ivM0_iv lo hi
  let Mp := ivM0p_iv T
  let omM := one.sub M
  let q := Iv.exp Fp.neg
  let P := one.sub q
  let logP := Iv.log P
  let logX := (Iv.log omM).add (logP.divPos omM)
  let X := Iv.exp logX
  let omX := one.sub X
  let logXp := ((Mp.divPos omM).mul ((logP.divPos omM).sub one)).add
    ((Fpp.divPos omM).mul (q.divPos P))
  let dPhi0 := (((((Iv.ofInt 2).mul Fp).add (Iv.log M)).add (one.sub T)).add
    (Iv.log omX)).add ((one.sub (T.mul (X.divPos omX))).mul logXp)
  decide (0 < lo ∧ lo ≤ hi ∧ hi ≤ ivScale ∧
          0 < Mm.lo ∧ Mm.hi < ivScale ∧ 0 < omMm.lo ∧ 0 < Pm.lo ∧ 0 < Xm.lo ∧ 0 < omXm.lo ∧
          0 < M.lo ∧ M.hi < ivScale ∧ 0 < omM.lo ∧ 0 < P.lo ∧ 0 < X.lo ∧ 0 < omX.lo ∧
          0 < (mvtBound Phi0_m dPhi0 lo hi).lo) &&
  Iv.logPtOk lo && Iv.logPtOk (ivScale + lo) &&
  Iv.logPtOk hi && Iv.logPtOk (ivScale + hi) &&
  Iv.logPtOk m && Iv.logPtOk (ivScale + m) &&
  Iv.logOk Mm && Iv.logOk omMm && Fpm.neg.expOk && Iv.logOk Pm && logXm.expOk && Iv.logOk omXm &&
  Iv.logOk M && Iv.logOk omM && Fp.neg.expOk && Iv.logOk P && logX.expOk && Iv.logOk omX

lemma iv_pos_of_lo_pos {I : Iv} {x : ℝ} (hlo : 0 < I.lo) (hx : I.Mem x) : 0 < x :=
  lt_of_lt_of_le (div_pos (by exact_mod_cast hlo) ivScale_pos) hx.1

lemma iv_lt_one_of_hi_lt {I : Iv} {x : ℝ} (hhi : I.hi < ivScale) (hx : I.Mem x) : x < 1 :=
  lt_of_le_of_lt hx.2 ((div_lt_one ivScale_pos).2 (by exact_mod_cast hhi))

set_option maxHeartbeats 400000 in
lemma checkPhi0Iv_sound {lo hi : ℤ} (hok : checkPhi0Iv lo hi = true) :
    ∀ t ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      let X := (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t)
      0 < X ∧ X < 1 ∧
      -(Real.log X + t * Real.log (M0Fn t) + t * Real.log (1 - X)) / 2 < FFn (2 / 25) t := by
  unfold checkPhi0Iv at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlo0, hlohi, hhi1,
    _hMm_lo, _hMm_hi, homMm_lo, _hPm_lo, _hXm_lo, _homXm_lo,
    hM_lo, hM_hi, homM_lo, hP_lo, _hX_lo, homX_lo, hpos_lo⟩,
    hok_lo⟩, hok_lo1⟩, hok_hi⟩, hok_hi1⟩, hok_m⟩, hok_m1⟩,
    hlogMm⟩, hlogomMm⟩, hexpFpm⟩, hlogPm⟩, h4'⟩, hlogomXm⟩,
    hlogM⟩, hlogomM⟩, hexpFp⟩, hlogP⟩, h8'⟩, hlogomX⟩
  set m : ℤ := (lo + hi) / 2
  set T : Iv := ⟨lo, hi⟩
  have hm0 : 0 < m := by dsimp [m]; omega
  have hm1 : m ≤ ivScale := by dsimp [m]; omega
  have hD := ivScale_pos
  have h1_mem : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have h2_mem : (Iv.ofInt 2).Mem (2 : ℝ) := by simpa using Iv.mem_ofInt 2
  set Fm := ivF_pt 2 25 m
  set Fpm := ivFp_pt 2 25 m
  set Mm := ivM0_pt m
  set omMm := (Iv.ofInt 1).sub Mm
  set qm := Iv.exp Fpm.neg
  set Pm := (Iv.ofInt 1).sub qm
  set logPm := Iv.log Pm
  set logXm := (Iv.log omMm).add (logPm.divPos omMm)
  set Xm := Iv.exp logXm
  set omXm := (Iv.ofInt 1).sub Xm
  set Fp : Iv := ⟨(ivFp_pt 2 25 hi).lo, (ivFp_pt 2 25 lo).hi⟩
  set Fpp := ivFpp_iv 2 25 T
  set M := ivM0_iv lo hi
  set Mp := ivM0p_iv T
  set omM := (Iv.ofInt 1).sub M
  set q := Iv.exp Fp.neg
  set P := (Iv.ofInt 1).sub q
  set logP := Iv.log P
  set logX := (Iv.log omM).add (logP.divPos omM)
  set X := Iv.exp logX
  set omX := (Iv.ofInt 1).sub X
  -- Midpoint membership
  set mr : ℝ := (m : ℝ) / (ivScale : ℝ)
  have hFm_mem : Fm.Mem (FFn (2 / 25) mr) := by
    simpa using mem_ivF_pt (bn := 2) (bd := 25) (by norm_num) hm0 hm1 hok_m hok_m1
  have hFpm_mem : Fpm.Mem (FFn' (2 / 25) mr) := by
    simpa using mem_ivFp_pt (bn := 2) (bd := 25) (by norm_num) hm0 hm1 hok_m hok_m1
  have hMm_mem : Mm.Mem (M0Fn mr) := mem_ivM0_pt hm0 hm1
  have homMm_mem : omMm.Mem (1 - M0Fn mr) := Iv.mem_sub h1_mem hMm_mem
  have hqm_mem : qm.Mem (Real.exp (-FFn' (2 / 25) mr)) := Iv.mem_exp_of_ok hexpFpm (Iv.mem_neg hFpm_mem)
  have hPm_mem : Pm.Mem (1 - Real.exp (-FFn' (2 / 25) mr)) := Iv.mem_sub h1_mem hqm_mem
  have hlogPm_mem : logPm.Mem (Real.log (1 - Real.exp (-FFn' (2 / 25) mr))) := Iv.mem_log hlogPm hPm_mem
  have hlogXm_mem : logXm.Mem (logXFn (2 / 25) M0Fn mr) :=
    Iv.mem_add (Iv.mem_log hlogomMm homMm_mem) (Iv.mem_divPos hlogPm_mem homMm_lo homMm_mem)
  have hXm_mem : Xm.Mem (Real.exp (logXFn (2 / 25) M0Fn mr)) := Iv.mem_exp_of_ok h4' hlogXm_mem
  have homXm_mem : omXm.Mem (1 - Real.exp (logXFn (2 / 25) M0Fn mr)) := Iv.mem_sub h1_mem hXm_mem
  let f : ℝ → ℝ := fun s => 2 * FFn (2 / 25) s + logXFn (2 / 25) M0Fn s + s * Real.log (M0Fn s) +
      s * Real.log (1 - Real.exp (logXFn (2 / 25) M0Fn s))
  let f' : ℝ → ℝ := fun s => 2 * FFn' (2 / 25) s + logXFn' (2 / 25) M0Fn M0Fn' s +
      Real.log (M0Fn s) + s * M0Fn' s / M0Fn s +
      Real.log (1 - Real.exp (logXFn (2 / 25) M0Fn s)) -
      s * (Real.exp (logXFn (2 / 25) M0Fn s) / (1 - Real.exp (logXFn (2 / 25) M0Fn s))) *
        logXFn' (2 / 25) M0Fn M0Fn' s
  set Phi0_m := (((Iv.ofInt 2).mul Fm).add logXm).add ((Iv.ofScaled m).mul ((Iv.log Mm).add (Iv.log omXm)))
  have hPhim_mem : Phi0_m.Mem (f mr) := by
    have heq : f mr = 2 * FFn (2 / 25) mr + logXFn (2 / 25) M0Fn mr +
        mr * (Real.log (M0Fn mr) + Real.log (1 - Real.exp (logXFn (2 / 25) M0Fn mr))) := by
      dsimp [f]; ring
    rw [heq]
    exact Iv.mem_add (Iv.mem_add (Iv.mem_mul h2_mem hFm_mem) hlogXm_mem)
      (Iv.mem_mul (mem_ofScaled m) (Iv.mem_add (Iv.mem_log hlogMm hMm_mem) (Iv.mem_log hlogomXm homXm_mem)))
  -- Derivative membership on [lo/D, hi/D]
  set logXp := ((Mp.divPos omM).mul ((logP.divPos omM).sub (Iv.ofInt 1))).add
    ((Fpp.divPos omM).mul (q.divPos P))
  set dPhi0 := (((((Iv.ofInt 2).mul Fp).add (Iv.log M)).add ((Iv.ofInt 1).sub T)).add
    (Iv.log omX)).add (((Iv.ofInt 1).sub (T.mul (X.divPos omX))).mul logXp)
  have hderiv_all : ∀ s ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      HasDerivAt f (f' s) s ∧ dPhi0.Mem (f' s) ∧
      0 < Real.exp (logXFn (2 / 25) M0Fn s) ∧ Real.exp (logXFn (2 / 25) M0Fn s) < 1 := by
    intro s hs
    have hsT : T.Mem s := hs
    have hs0 : 0 < s := lt_of_lt_of_le (div_pos (by exact_mod_cast hlo0) hD) hs.1
    have hs1 : s ≤ 1 := hs.2.trans ((div_le_one hD).2 (by exact_mod_cast hhi1))
    have hFp_mem : Fp.Mem (FFn' (2 / 25) s) := by
      have hlo_p : (ivFp_pt 2 25 lo).Mem (FFn' (2 / 25) ((lo : ℝ) / (ivScale : ℝ))) := by
        simpa using mem_ivFp_pt (bn := 2) (bd := 25) (by norm_num) hlo0 (hlohi.trans hhi1) hok_lo hok_lo1
      have hhi_p : (ivFp_pt 2 25 hi).Mem (FFn' (2 / 25) ((hi : ℝ) / (ivScale : ℝ))) := by
        simpa using mem_ivFp_pt (bn := 2) (bd := 25) (by norm_num) (by omega) hhi1 hok_hi hok_hi1
      have hanti := FFn'_anti (b := (2 : ℝ) / 25) (by norm_num) (by norm_num)
      have hlo_m : ((lo : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos (by exact_mod_cast hlo0) hD, (div_le_one hD).2 (by exact_mod_cast (hlohi.trans hhi1))⟩
      have hhi_m : ((hi : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos (by exact_mod_cast (by omega : 0 < hi)) hD, (div_le_one hD).2 (by exact_mod_cast hhi1)⟩
      exact ⟨hhi_p.1.trans (hanti ⟨hs0, hs1⟩ hhi_m hs.2), (hanti hlo_m ⟨hs0, hs1⟩ hs.1).trans hlo_p.2⟩
    have hFpp_mem : Fpp.Mem (FFn'' (2 / 25) s) := by
      simpa using mem_ivFpp_iv (bn := 2) (bd := 25) (by norm_num) hlo0 hhi1 hsT
    have hM_mem : M.Mem (M0Fn s) := mem_ivM0_iv hlo0 hlohi hhi1 hsT
    have hMp_mem : Mp.Mem (M0Fn' s) := mem_ivM0p_iv hlo0 hhi1 hsT
    have homM_mem : omM.Mem (1 - M0Fn s) := Iv.mem_sub h1_mem hM_mem
    have hq_mem : q.Mem (Real.exp (-FFn' (2 / 25) s)) := Iv.mem_exp_of_ok hexpFp (Iv.mem_neg hFp_mem)
    have hP_mem : P.Mem (1 - Real.exp (-FFn' (2 / 25) s)) := Iv.mem_sub h1_mem hq_mem
    have hlogP_mem : logP.Mem (Real.log (1 - Real.exp (-FFn' (2 / 25) s))) := Iv.mem_log hlogP hP_mem
    have hlogX_mem : logX.Mem (logXFn (2 / 25) M0Fn s) :=
      Iv.mem_add (Iv.mem_log hlogomM homM_mem) (Iv.mem_divPos hlogP_mem homM_lo homM_mem)
    have hX_mem : X.Mem (Real.exp (logXFn (2 / 25) M0Fn s)) := Iv.mem_exp_of_ok h8' hlogX_mem
    have homX_mem : omX.Mem (1 - Real.exp (logXFn (2 / 25) M0Fn s)) := Iv.mem_sub h1_mem hX_mem
    have hX0 : 0 < Real.exp (logXFn (2 / 25) M0Fn s) := Real.exp_pos _
    have hX1 : Real.exp (logXFn (2 / 25) M0Fn s) < 1 := by
      have := iv_pos_of_lo_pos homX_lo homX_mem; linarith
    have hM0_s : 0 < M0Fn s := iv_pos_of_lo_pos hM_lo hM_mem
    have hM1_s : M0Fn s < 1 := iv_lt_one_of_hi_lt hM_hi hM_mem
    have hFp_pos : 0 < FFn' (2 / 25) s := FFn'_pos (by norm_num) (by norm_num) hs0 hs1
    have hd := hasDerivAt_ESFn hs0 (hasDerivAt_M0Fn s) hM0_s hM1_s hFp_pos hX1
    have hlogXp_mem : logXp.Mem (logXFn' (2 / 25) M0Fn M0Fn' s) := by
      unfold logXFn'
      exact Iv.mem_add
        (Iv.mem_mul (Iv.mem_divPos hMp_mem homM_lo homM_mem)
          (Iv.mem_sub (Iv.mem_divPos hlogP_mem homM_lo homM_mem) h1_mem))
        (Iv.mem_mul (Iv.mem_divPos hFpp_mem homM_lo homM_mem)
          (Iv.mem_divPos hq_mem hP_lo hP_mem))
    have hd_mem : dPhi0.Mem (f' s) := by
      have heq : f' s = 2 * FFn' (2 / 25) s + Real.log (M0Fn s) + (1 - s) +
          Real.log (1 - Real.exp (logXFn (2 / 25) M0Fn s)) +
          (1 - s * (Real.exp (logXFn (2 / 25) M0Fn s) / (1 - Real.exp (logXFn (2 / 25) M0Fn s)))) *
            logXFn' (2 / 25) M0Fn M0Fn' s := by
        dsimp [f']; rw [M0_t_mul_deriv_div hs0]; ring
      rw [heq]
      exact Iv.mem_add
        (Iv.mem_add (Iv.mem_add (Iv.mem_add (Iv.mem_mul h2_mem hFp_mem) (Iv.mem_log hlogM hM_mem))
          (Iv.mem_sub h1_mem hsT)) (Iv.mem_log hlogomX homX_mem))
        (Iv.mem_mul (Iv.mem_sub h1_mem (Iv.mem_mul hsT (Iv.mem_divPos hX_mem homX_lo homX_mem))) hlogXp_mem)
    exact ⟨hd, hd_mem, hX0, hX1⟩
  intro t ht
  have hmvt := mem_mvtBound hlohi hPhim_mem (fun s hs => ⟨(hderiv_all s hs).1, (hderiv_all s hs).2.1⟩) ht
  have hft_pos : 0 < f t := iv_pos_of_lo_pos hpos_lo hmvt
  have ht0 : 0 < t := lt_of_lt_of_le (div_pos (by exact_mod_cast hlo0) hD) ht.1
  have ht1 : t ≤ 1 := ht.2.trans ((div_le_one hD).2 (by exact_mod_cast hhi1))
  have hM1_t : M0Fn t < 1 := by
    have : M0Fn t ≤ 1 * Real.exp (-t) := mul_le_mul_of_nonneg_right ht1 (Real.exp_pos _).le
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    unfold M0Fn at *; linarith
  have hFp_t : 0 < FFn' (2 / 25) t := FFn'_pos (by norm_num) (by norm_num) ht0 ht1
  have hX_eq : (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t) =
      Real.exp (logXFn (2 / 25) M0Fn t) := by
    have hXpos : 0 < (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t) :=
      mul_pos (Real.rpow_pos_of_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))) _) (sub_pos.2 hM1_t)
    rw [← log_X_eq_logXFn hM1_t hFp_t, Real.exp_log hXpos]
  dsimp only
  rw [hX_eq, Real.log_exp]
  refine ⟨(hderiv_all t ht).2.2.1, (hderiv_all t ht).2.2.2, ?_⟩
  dsimp [f] at hft_pos
  linarith

/- ### Computable check for Phi1 on [lo/D, hi/D] and its soundness proof -/

def ivF08_1 : Iv := ivF_pt 2 25 ivScale
def ivFp08_1 : Iv := ivFp_pt 2 25 ivScale
def ivLogA1 : Iv := ivFp08_1.neg
def ivLogB1 : Iv := ivFp08_1.sub ivF08_1

def checkPhi1Iv (e : ℤ × ℤ × ℕ × ℤ) : Bool :=
  let (lo, hi, md, t0) := e
  let one := Iv.ofInt 1
  let m := (lo + hi) / 2
  let T : Iv := ⟨lo, hi⟩
  let Fm := ivF_pt 3 100 m
  let Fpm := ivFp_pt 3 100 m
  let Mm := ivM1_pt m
  let omMm := one.sub Mm
  let qm := Iv.exp Fpm.neg
  let Pm := one.sub qm
  let logPm := Iv.log Pm
  let logXm := (Iv.log omMm).add (logPm.divPos omMm)
  let logMm := Iv.log Mm
  let Fp : Iv := ⟨(ivFp_pt 3 100 hi).lo, (ivFp_pt 3 100 lo).hi⟩
  let Fpp := ivFpp_iv 3 100 T
  let M := ivM1_iv T
  let Mp := ivM1p_iv T
  let omM := one.sub M
  let q := Iv.exp Fp.neg
  let P := one.sub q
  let logP := Iv.log P
  let logM := Iv.log M
  let logXp := ((Mp.divPos omM).mul ((logP.divPos omM).sub one)).add
    ((Fpp.divPos omM).mul (q.divPos P))
  let logX := mvtBound logXm logXp lo hi
  let tMpM := (one.sub ((Iv.ofRat 2 3).mul T)).sub ((Iv.ofRat 3 5).mul T.sqNonneg)
  let base_m := (((Iv.ofInt 2).mul Fm).add logXm).add ((Iv.ofScaled m).mul logMm)
  let dbase := ((((Iv.ofInt 2).mul Fp).add logXp).add logM).add tMpM
  let commonOk : Bool :=
    decide (0 < lo ∧ lo ≤ hi ∧ hi ≤ ivScale ∧
            0 < Mm.lo ∧ Mm.hi < ivScale ∧ 0 < omMm.lo ∧ 0 < Pm.lo ∧
            0 < M.lo ∧ M.hi < ivScale ∧ 0 < omM.lo ∧ 0 < P.lo) &&
    Iv.logPtOk lo && Iv.logPtOk (ivScale + lo) &&
    Iv.logPtOk hi && Iv.logPtOk (ivScale + hi) &&
    Iv.logPtOk m && Iv.logPtOk (ivScale + m) &&
    Iv.logOk Mm && Iv.logOk omMm && Fpm.neg.expOk && Iv.logOk Pm &&
    Iv.logOk M && Iv.logOk omM && Fp.neg.expOk && Iv.logOk P
  commonOk &&
  match md with
  | 0 =>
    let Xm := Iv.exp logXm
    let X := Iv.exp logX
    let omXm := one.sub Xm
    let omX := one.sub X
    let val0_m := base_m.add ((Iv.ofScaled m).mul (Iv.log omXm))
    let dval0 := (dbase.add (Iv.log omX)).sub ((T.mul (X.divPos omX)).mul logXp)
    decide (0 < Xm.lo ∧ 0 < omXm.lo ∧ 0 < X.lo ∧ 0 < omX.lo ∧ 0 < (mvtBound val0_m dval0 lo hi).lo) &&
    logXm.expOk && logX.expOk && Iv.logOk omXm && Iv.logOk omX
  | 1 =>
    let mid_m := (((Iv.ofInt 2).mul Fm).add ((one.sub (Iv.ofScaled m)).mul logXm)).add
      ((Iv.ofScaled m).mul (logMm.sub ivF08_1))
    let dmid := ((((((Iv.ofInt 2).mul Fp).add ((one.sub T).mul logXp)).sub logX).add logM).add
      tMpM).sub ivF08_1
    decide (ivLogA1.hi ≤ logX.lo ∧ logX.hi ≤ ivLogB1.lo ∧ 0 < (mvtBound mid_m dmid lo hi).lo)
  | 2 =>
    let Fp08_t := ivFp_pt 2 25 t0
    let F08_t := ivF_pt 2 25 t0
    let logBt := ((Iv.ofScaled t0).mul Fp08_t).sub F08_t
    let val2_m := base_m.add ((Iv.ofScaled m).mul logBt)
    let dval2 := dbase.add logBt
    decide (0 < t0 ∧ t0 ≤ ivScale ∧ logX.hi ≤ -Fp08_t.hi ∧ 0 < (mvtBound val2_m dval2 lo hi).lo) &&
    Iv.logPtOk t0 && Iv.logPtOk (ivScale + t0)
  | 3 =>
    let Fp08_t := ivFp_pt 2 25 t0
    let F08_t := ivF_pt 2 25 t0
    let logBt := ((Iv.ofScaled t0).mul Fp08_t).sub F08_t
    let logAt := Fp08_t.neg
    let val3_m := base_m.add ((Iv.ofScaled m).mul logAt)
    let dval3 := dbase.add logAt
    decide (0 < t0 ∧ t0 ≤ ivScale ∧ logX.hi ≤ logBt.lo ∧ 0 < (mvtBound val3_m dval3 lo hi).lo) &&
    Iv.logPtOk t0 && Iv.logPtOk (ivScale + t0)
  | 4 =>
    let mid_m := (((Iv.ofInt 2).mul Fm).add ((one.sub (Iv.ofScaled m)).mul logXm)).add
      ((Iv.ofScaled m).mul (logMm.sub ivF08_1))
    let dmid := ((((((Iv.ofInt 2).mul Fp).add ((one.sub T).mul logXp)).sub logX).add logM).add
      tMpM).sub ivF08_1
    let cA_m := base_m.add ((Iv.ofScaled m).mul ivLogB1)
    let dcA := dbase.add ivLogB1
    decide (logX.hi ≤ ivLogB1.lo ∧ 0 < (mvtBound mid_m dmid lo hi).lo ∧
      0 < (mvtBound cA_m dcA lo hi).lo)
  | _ => false

lemma mem_ivF08_1 : ivF08_1.Mem (FFn (2 / 25) 1) := by
  have h1 : ((ivScale : ℤ) : ℝ) / (ivScale : ℝ) = 1 := div_self ivScale_pos.ne'
  have hok1 : Iv.logPtOk ivScale = true := by decide
  have hok2 : Iv.logPtOk (ivScale + ivScale) = true := by decide
  have h := mem_ivF_pt (bn := 2) (bd := 25) (a := ivScale) (by norm_num) ivScale_pos_int le_rfl hok1 hok2
  simpa [ivF08_1, h1] using h

lemma mem_ivFp08_1 : ivFp08_1.Mem (FFn' (2 / 25) 1) := by
  have h1 : ((ivScale : ℤ) : ℝ) / (ivScale : ℝ) = 1 := div_self ivScale_pos.ne'
  have hok1 : Iv.logPtOk ivScale = true := by decide
  have hok2 : Iv.logPtOk (ivScale + ivScale) = true := by decide
  have h := mem_ivFp_pt (bn := 2) (bd := 25) (a := ivScale) (by norm_num) ivScale_pos_int le_rfl hok1 hok2
  simpa [ivFp08_1, h1] using h

lemma mem_ivLogA1 : ivLogA1.Mem (-FFn' (2 / 25) 1) := Iv.mem_neg mem_ivFp08_1

lemma mem_ivLogB1 : ivLogB1.Mem (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) := by
  have heq : -(FFn (2 / 25) 1 - FFn' (2 / 25) 1) = FFn' (2 / 25) 1 - FFn (2 / 25) 1 := by ring
  rw [heq]
  exact Iv.mem_sub mem_ivFp08_1 mem_ivF08_1

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
lemma checkPhi1Iv_sound
    (hInR_AB : ∀ t ∈ Ioc (0 : ℝ) 1,
      InR (Real.exp (-FFn' (2 / 25) t)) (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) ∧
      InR (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) (Real.exp (-FFn' (2 / 25) t)))
    (hInR_mid : ∀ x : ℝ,
      Real.exp (-FFn' (2 / 25) 1) ≤ x → x ≤ Real.exp (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) →
      0 < Real.exp (-FFn (2 / 25) 1) / x ∧ Real.exp (-FFn (2 / 25) 1) / x < 1 ∧
      InR x (Real.exp (-FFn (2 / 25) 1) / x))
    {e : ℤ × ℤ × ℕ × ℤ} (hok : checkPhi1Iv e = true) :
    ∀ t ∈ Icc ((e.1 : ℝ) / (ivScale : ℝ)) ((e.2.1 : ℝ) / (ivScale : ℝ)),
      ∃ y : ℝ, 0 < y ∧ y < 1 ∧
        let X := (1 - Real.exp (-FFn' (3 / 100) t)) ^ (1 / (1 - M1Fn t)) * (1 - M1Fn t)
        InR X y ∧
        -(Real.log X + t * Real.log (M1Fn t) + t * Real.log y) / 2 < FFn (3 / 100) t := by
  rcases e with ⟨lo, hi, md, t0⟩
  unfold checkPhi1Iv at hok
  dsimp only at hok
  rw [Bool.and_eq_true] at hok
  rcases hok with ⟨hcomm, hbranch⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcomm
  rcases hcomm with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlo0, hlohi, hhi1,
    _hMm_lo, _hMm_hi, homMm_lo, _hPm_lo,
    hM_lo, hM_hi, homM_lo, hP_lo⟩,
    hok_lo⟩, hok_lo1⟩, hok_hi⟩, hok_hi1⟩, hok_m⟩, hok_m1⟩,
    hlogMm⟩, hlogomMm⟩, hexpFpm⟩, hlogPm⟩,
    hlogM⟩, hlogomM⟩, hexpFp⟩, hlogP⟩
  set m : ℤ := (lo + hi) / 2
  set T : Iv := ⟨lo, hi⟩
  have hm0 : 0 < m := by dsimp [m]; omega
  have hm1 : m ≤ ivScale := by dsimp [m]; omega
  have hTlo0 : 0 ≤ T.lo := by dsimp [T]; omega
  have hThi1 : T.hi ≤ ivScale := by dsimp [T]; omega
  have hTle : T.lo ≤ T.hi := by dsimp [T]; omega
  have hD := ivScale_pos
  have h1_mem : (Iv.ofInt 1).Mem (1 : ℝ) := by simpa using Iv.mem_ofInt 1
  have h2_mem : (Iv.ofInt 2).Mem (2 : ℝ) := by simpa using Iv.mem_ofInt 2
  set Fm := ivF_pt 3 100 m
  set Fpm := ivFp_pt 3 100 m
  set Mm := ivM1_pt m
  set omMm := (Iv.ofInt 1).sub Mm
  set qm := Iv.exp Fpm.neg
  set Pm := (Iv.ofInt 1).sub qm
  set logPm := Iv.log Pm
  set logXm := (Iv.log omMm).add (logPm.divPos omMm)
  set logMm := Iv.log Mm
  set Fp : Iv := ⟨(ivFp_pt 3 100 hi).lo, (ivFp_pt 3 100 lo).hi⟩
  set Fpp := ivFpp_iv 3 100 T
  set M := ivM1_iv T
  set Mp := ivM1p_iv T
  set omM := (Iv.ofInt 1).sub M
  set q := Iv.exp Fp.neg
  set P := (Iv.ofInt 1).sub q
  set logP := Iv.log P
  set logM := Iv.log M
  set logXp := ((Mp.divPos omM).mul ((logP.divPos omM).sub (Iv.ofInt 1))).add
    ((Fpp.divPos omM).mul (q.divPos P))
  set logX := mvtBound logXm logXp lo hi
  set tMpM := ((Iv.ofInt 1).sub ((Iv.ofRat 2 3).mul T)).sub ((Iv.ofRat 3 5).mul T.sqNonneg)
  set base_m := (((Iv.ofInt 2).mul Fm).add logXm).add ((Iv.ofScaled m).mul logMm)
  set dbase := ((((Iv.ofInt 2).mul Fp).add logXp).add logM).add tMpM
  -- Establish common midpoint and interval memberships
  set mr : ℝ := (m : ℝ) / (ivScale : ℝ)
  have hFm_mem : Fm.Mem (FFn (3 / 100) mr) := by
    simpa using mem_ivF_pt (bn := 3) (bd := 100) (by norm_num) hm0 hm1 hok_m hok_m1
  have hFpm_mem : Fpm.Mem (FFn' (3 / 100) mr) := by
    simpa using mem_ivFp_pt (bn := 3) (bd := 100) (by norm_num) hm0 hm1 hok_m hok_m1
  have hMm_mem : Mm.Mem (M1Fn mr) := mem_ivM1_pt (by omega) hm1
  have homMm_mem : omMm.Mem (1 - M1Fn mr) := Iv.mem_sub h1_mem hMm_mem
  have hqm_mem : qm.Mem (Real.exp (-FFn' (3 / 100) mr)) := Iv.mem_exp_of_ok hexpFpm (Iv.mem_neg hFpm_mem)
  have hPm_mem : Pm.Mem (1 - Real.exp (-FFn' (3 / 100) mr)) := Iv.mem_sub h1_mem hqm_mem
  have hlogPm_mem : logPm.Mem (Real.log (1 - Real.exp (-FFn' (3 / 100) mr))) := Iv.mem_log hlogPm hPm_mem
  have hlogXm_mem : logXm.Mem (logXFn (3 / 100) M1Fn mr) :=
    Iv.mem_add (Iv.mem_log hlogomMm homMm_mem) (Iv.mem_divPos hlogPm_mem homMm_lo homMm_mem)
  have hlogMm_mem : logMm.Mem (Real.log (M1Fn mr)) := Iv.mem_log hlogMm hMm_mem
  have hbase_m_mem : base_m.Mem (2 * FFn (3 / 100) mr + logXFn (3 / 100) M1Fn mr + mr * Real.log (M1Fn mr)) :=
    Iv.mem_add (Iv.mem_add (Iv.mem_mul h2_mem hFm_mem) hlogXm_mem) (Iv.mem_mul (mem_ofScaled m) hlogMm_mem)
  -- Per-point properties on [lo/D, hi/D]
  have hpt : ∀ s ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      0 < s ∧ s ≤ 1 ∧ 0 < M1Fn s ∧ M1Fn s < 1 ∧ 0 < FFn' (3 / 100) s ∧
      Fp.Mem (FFn' (3 / 100) s) ∧ logM.Mem (Real.log (M1Fn s)) ∧
      logXp.Mem (logXFn' (3 / 100) M1Fn M1Fn' s) ∧
      tMpM.Mem (s * M1Fn' s / M1Fn s) ∧
      dbase.Mem (2 * FFn' (3 / 100) s + logXFn' (3 / 100) M1Fn M1Fn' s +
        Real.log (M1Fn s) + s * M1Fn' s / M1Fn s) := by
    intro s hs
    have hsT : T.Mem s := hs
    have hs0 : 0 < s := lt_of_lt_of_le (div_pos (by exact_mod_cast hlo0) hD) hs.1
    have hs1 : s ≤ 1 := hs.2.trans ((div_le_one hD).2 (by exact_mod_cast hhi1))
    have hFp_mem : Fp.Mem (FFn' (3 / 100) s) := by
      have hlo_p : (ivFp_pt 3 100 lo).Mem (FFn' (3 / 100) ((lo : ℝ) / (ivScale : ℝ))) := by
        simpa using mem_ivFp_pt (bn := 3) (bd := 100) (by norm_num) hlo0 (hlohi.trans hhi1) hok_lo hok_lo1
      have hhi_p : (ivFp_pt 3 100 hi).Mem (FFn' (3 / 100) ((hi : ℝ) / (ivScale : ℝ))) := by
        simpa using mem_ivFp_pt (bn := 3) (bd := 100) (by norm_num) (by omega) hhi1 hok_hi hok_hi1
      have hanti := FFn'_anti (b := (3 : ℝ) / 100) (by norm_num) (by norm_num)
      have hlo_m : ((lo : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos (by exact_mod_cast hlo0) hD, (div_le_one hD).2 (by exact_mod_cast (hlohi.trans hhi1))⟩
      have hhi_m : ((hi : ℝ) / (ivScale : ℝ)) ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos (by exact_mod_cast (by omega : 0 < hi)) hD, (div_le_one hD).2 (by exact_mod_cast hhi1)⟩
      exact ⟨hhi_p.1.trans (hanti ⟨hs0, hs1⟩ hhi_m hs.2), (hanti hlo_m ⟨hs0, hs1⟩ hs.1).trans hlo_p.2⟩
    have hFpp_mem : Fpp.Mem (FFn'' (3 / 100) s) := by
      simpa using mem_ivFpp_iv (bn := 3) (bd := 100) (by norm_num) hlo0 hhi1 hsT
    have hM_mem : M.Mem (M1Fn s) := mem_ivM1_iv hTlo0 hThi1 hTle hsT
    have hMp_mem : Mp.Mem (M1Fn' s) := mem_ivM1p_iv hTlo0 hThi1 hTle hsT
    have homM_mem : omM.Mem (1 - M1Fn s) := Iv.mem_sub h1_mem hM_mem
    have hq_mem : q.Mem (Real.exp (-FFn' (3 / 100) s)) := Iv.mem_exp_of_ok hexpFp (Iv.mem_neg hFp_mem)
    have hP_mem : P.Mem (1 - Real.exp (-FFn' (3 / 100) s)) := Iv.mem_sub h1_mem hq_mem
    have hlogP_mem : logP.Mem (Real.log (1 - Real.exp (-FFn' (3 / 100) s))) := Iv.mem_log hlogP hP_mem
    have hlogM_mem : logM.Mem (Real.log (M1Fn s)) := Iv.mem_log hlogM hM_mem
    have hM0_s : 0 < M1Fn s := iv_pos_of_lo_pos hM_lo hM_mem
    have hM1_s : M1Fn s < 1 := iv_lt_one_of_hi_lt hM_hi hM_mem
    have hFp_pos : 0 < FFn' (3 / 100) s := FFn'_pos (by norm_num) (by norm_num) hs0 hs1
    have hlogXp_mem : logXp.Mem (logXFn' (3 / 100) M1Fn M1Fn' s) := by
      unfold logXFn'
      exact Iv.mem_add
        (Iv.mem_mul (Iv.mem_divPos hMp_mem homM_lo homM_mem)
          (Iv.mem_sub (Iv.mem_divPos hlogP_mem homM_lo homM_mem) h1_mem))
        (Iv.mem_mul (Iv.mem_divPos hFpp_mem homM_lo homM_mem)
          (Iv.mem_divPos hq_mem hP_lo hP_mem))
    have htMpM_mem : tMpM.Mem (s * M1Fn' s / M1Fn s) := by
      rw [M1_t_mul_deriv_div hs0]
      have hT2 : T.sqNonneg.Mem (s ^ 2) := by rw [sq]; exact Iv.mem_sqNonneg hTlo0 hsT
      have hr1 : (Iv.ofRat 2 3).Mem ((2 : ℝ) / 3) := by
        simpa using Iv.mem_ofRat (p := 2) (q := 3) (by norm_num)
      have hr2 : (Iv.ofRat 3 5).Mem ((3 : ℝ) / 5) := by
        simpa using Iv.mem_ofRat (p := 3) (q := 5) (by norm_num)
      exact Iv.mem_sub (Iv.mem_sub h1_mem (Iv.mem_mul hr1 hsT)) (Iv.mem_mul hr2 hT2)
    have hdbase_mem : dbase.Mem (2 * FFn' (3 / 100) s + logXFn' (3 / 100) M1Fn M1Fn' s +
        Real.log (M1Fn s) + s * M1Fn' s / M1Fn s) :=
      Iv.mem_add (Iv.mem_add (Iv.mem_add (Iv.mem_mul h2_mem hFp_mem) hlogXp_mem) hlogM_mem) htMpM_mem
    exact ⟨hs0, hs1, hM0_s, hM1_s, hFp_pos, hFp_mem, hlogM_mem, hlogXp_mem, htMpM_mem, hdbase_mem⟩
  -- MVT membership of logX on [lo/D, hi/D]
  have hlogX_mem : ∀ s ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      logX.Mem (logXFn (3 / 100) M1Fn s) := fun s hs =>
    mem_mvtBound hlohi hlogXm_mem (fun u hu => by
      obtain ⟨hu0, _, _, huM1, huFp, _, _, hulogXp, _, _⟩ := hpt u hu
      exact ⟨hasDerivAt_logXFn hu0 (hasDerivAt_M1Fn u) huM1 huFp, hulogXp⟩) hs
  -- Helper: real X equals exp(logXFn)
  have hX_eq_exp : ∀ s ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
      (1 - Real.exp (-FFn' (3 / 100) s)) ^ (1 / (1 - M1Fn s)) * (1 - M1Fn s) =
      Real.exp (logXFn (3 / 100) M1Fn s) := by
    intro s hs
    obtain ⟨_, _, _, hsM1, hsFp, _, _, _, _, _⟩ := hpt s hs
    have hXpos : 0 < (1 - Real.exp (-FFn' (3 / 100) s)) ^ (1 / (1 - M1Fn s)) * (1 - M1Fn s) :=
      mul_pos (Real.rpow_pos_of_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))) _) (sub_pos.2 hsM1)
    rw [← log_X_eq_logXFn hsM1 hsFp, Real.exp_log hXpos]
  -- Helper for constant logY = c bound
  have hconst_pos : ∀ (C : Iv) (c : ℝ), C.Mem c →
      0 < (mvtBound (base_m.add ((Iv.ofScaled m).mul C)) (dbase.add C) lo hi).lo →
      ∀ t ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
        0 < 2 * FFn (3 / 100) t + logXFn (3 / 100) M1Fn t + t * Real.log (M1Fn t) + t * c := by
    intro C c hC hpos t ht
    have hvm : (base_m.add ((Iv.ofScaled m).mul C)).Mem
        (2 * FFn (3 / 100) mr + logXFn (3 / 100) M1Fn mr + mr * Real.log (M1Fn mr) + mr * c) :=
      Iv.mem_add hbase_m_mem (Iv.mem_mul (mem_ofScaled m) hC)
    have hmvt := mem_mvtBound (f := fun s => 2 * FFn (3 / 100) s + logXFn (3 / 100) M1Fn s +
        s * Real.log (M1Fn s) + s * c)
      (f' := fun s => 2 * FFn' (3 / 100) s + logXFn' (3 / 100) M1Fn M1Fn' s +
        Real.log (M1Fn s) + s * M1Fn' s / M1Fn s + c)
      hlohi hvm (fun s hs => by
        obtain ⟨hs0, _, hsM0, hsM1, hsFp, _, _, _, _, hdb⟩ := hpt s hs
        exact ⟨hasDerivAt_constYFn hs0 (hasDerivAt_M1Fn s) hsM0 hsM1 hsFp, Iv.mem_add hdb hC⟩) ht
    exact iv_pos_of_lo_pos hpos hmvt
  -- Helper for Mid bound
  have hmid_pos :
      0 < (mvtBound
        ((((Iv.ofInt 2).mul Fm).add (((Iv.ofInt 1).sub (Iv.ofScaled m)).mul logXm)).add
          ((Iv.ofScaled m).mul (logMm.sub ivF08_1)))
        (((((((Iv.ofInt 2).mul Fp).add (((Iv.ofInt 1).sub T).mul logXp)).sub logX).add logM).add
          tMpM).sub ivF08_1) lo hi).lo →
      ∀ t ∈ Icc ((lo : ℝ) / (ivScale : ℝ)) ((hi : ℝ) / (ivScale : ℝ)),
        0 < 2 * FFn (3 / 100) t + (1 - t) * logXFn (3 / 100) M1Fn t +
            t * (Real.log (M1Fn t) - FFn (2 / 25) 1) := by
    intro hpos t ht
    have hvm := Iv.mem_add
      (Iv.mem_add (Iv.mem_mul h2_mem hFm_mem) (Iv.mem_mul (Iv.mem_sub h1_mem (mem_ofScaled m)) hlogXm_mem))
      (Iv.mem_mul (mem_ofScaled m) (Iv.mem_sub hlogMm_mem mem_ivF08_1))
    have hmvt := mem_mvtBound (f := fun s => 2 * FFn (3 / 100) s + (1 - s) * logXFn (3 / 100) M1Fn s +
        s * (Real.log (M1Fn s) - FFn (2 / 25) 1))
      (f' := fun s => 2 * FFn' (3 / 100) s + (1 - s) * logXFn' (3 / 100) M1Fn M1Fn' s -
        logXFn (3 / 100) M1Fn s + Real.log (M1Fn s) + s * M1Fn' s / M1Fn s - FFn (2 / 25) 1)
      hlohi hvm (fun s hs => by
        have hsT : T.Mem s := hs
        obtain ⟨hs0, _, hsM0, hsM1, hsFp, hFp_m, hlogM_m, hlogXp_m, htMpM_m, _⟩ := hpt s hs
        refine ⟨hasDerivAt_MidFn hs0 (hasDerivAt_M1Fn s) hsM0 hsM1 hsFp, ?_⟩
        exact Iv.mem_sub (Iv.mem_add (Iv.mem_add (Iv.mem_sub (Iv.mem_add (Iv.mem_mul h2_mem hFp_m)
          (Iv.mem_mul (Iv.mem_sub h1_mem hsT) hlogXp_m)) (hlogX_mem s hs)) hlogM_m) htMpM_m) mem_ivF08_1) ht
    exact iv_pos_of_lo_pos hpos hmvt
  -- Dispatch on mode md
  match md with
  | 0 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbranch
    rcases hbranch with ⟨⟨⟨⟨⟨_hXm_lo, _homXm_lo, _hX_lo, homX_lo, hpos⟩, hexpXm⟩, hexpX⟩, hlogomXm⟩, hlogomX⟩
    set Xm := Iv.exp logXm
    set X := Iv.exp logX
    set omXm := (Iv.ofInt 1).sub Xm
    set omX := (Iv.ofInt 1).sub X
    have hXm_mem : Xm.Mem (Real.exp (logXFn (3 / 100) M1Fn mr)) := Iv.mem_exp_of_ok hexpXm hlogXm_mem
    have homXm_mem : omXm.Mem (1 - Real.exp (logXFn (3 / 100) M1Fn mr)) := Iv.mem_sub h1_mem hXm_mem
    have hvm := Iv.mem_add hbase_m_mem (Iv.mem_mul (mem_ofScaled m) (Iv.mem_log hlogomXm homXm_mem))
    intro t ht
    have hX_t : X.Mem (Real.exp (logXFn (3 / 100) M1Fn t)) := Iv.mem_exp_of_ok hexpX (hlogX_mem t ht)
    have h1mX_pos : 0 < 1 - Real.exp (logXFn (3 / 100) M1Fn t) :=
      iv_pos_of_lo_pos homX_lo (Iv.mem_sub h1_mem hX_t)
    have hX_lt1 : Real.exp (logXFn (3 / 100) M1Fn t) < 1 := by linarith
    have hmvt := mem_mvtBound
      (f := fun s => 2 * FFn (3 / 100) s + logXFn (3 / 100) M1Fn s + s * Real.log (M1Fn s) +
        s * Real.log (1 - Real.exp (logXFn (3 / 100) M1Fn s)))
      (f' := fun s => 2 * FFn' (3 / 100) s + logXFn' (3 / 100) M1Fn M1Fn' s +
        Real.log (M1Fn s) + s * M1Fn' s / M1Fn s +
        Real.log (1 - Real.exp (logXFn (3 / 100) M1Fn s)) -
        s * (Real.exp (logXFn (3 / 100) M1Fn s) / (1 - Real.exp (logXFn (3 / 100) M1Fn s))) *
          logXFn' (3 / 100) M1Fn M1Fn' s)
      hlohi hvm (fun s hs => by
        have hsT : T.Mem s := hs
        obtain ⟨hs0, _, hsM0, hsM1, hsFp, _, _, hlogXp_m, _, hdb⟩ := hpt s hs
        have hXs : X.Mem (Real.exp (logXFn (3 / 100) M1Fn s)) := Iv.mem_exp_of_ok hexpX (hlogX_mem s hs)
        have homXs : omX.Mem (1 - Real.exp (logXFn (3 / 100) M1Fn s)) := Iv.mem_sub h1_mem hXs
        have hXs1 : Real.exp (logXFn (3 / 100) M1Fn s) < 1 := by
          have := iv_pos_of_lo_pos homX_lo homXs; linarith
        refine ⟨hasDerivAt_ESFn hs0 (hasDerivAt_M1Fn s) hsM0 hsM1 hsFp hXs1, ?_⟩
        exact Iv.mem_sub (Iv.mem_add hdb (Iv.mem_log hlogomX homXs))
          (Iv.mem_mul (Iv.mem_mul hsT (Iv.mem_divPos hXs homX_lo homXs)) hlogXp_m)) ht
    have hval := iv_pos_of_lo_pos hpos hmvt
    refine ⟨1 - Real.exp (logXFn (3 / 100) M1Fn t), h1mX_pos, by linarith [Real.exp_pos (logXFn (3 / 100) M1Fn t)], ?_, ?_⟩
    · rw [hX_eq_exp t ht]
      exact inR_es (Real.exp_pos _) hX_lt1
    · rw [hX_eq_exp t ht, Real.log_exp]; linarith
  | 1 =>
    simp only [decide_eq_true_eq] at hbranch
    rcases hbranch with ⟨hgeA, hleB, hpos⟩
    intro t ht
    have hlogX_t := hlogX_mem t ht
    have hge_a : Real.exp (-FFn' (2 / 25) 1) ≤ Real.exp (logXFn (3 / 100) M1Fn t) := by
      apply Real.exp_le_exp.2
      calc -FFn' (2 / 25) 1 ≤ (ivLogA1.hi : ℝ) / (ivScale : ℝ) := mem_ivLogA1.2
        _ ≤ (logX.lo : ℝ) / (ivScale : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hgeA) hD.le
        _ ≤ logXFn (3 / 100) M1Fn t := hlogX_t.1
    have hle_b : Real.exp (logXFn (3 / 100) M1Fn t) ≤ Real.exp (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) := by
      apply Real.exp_le_exp.2
      calc logXFn (3 / 100) M1Fn t ≤ (logX.hi : ℝ) / (ivScale : ℝ) := hlogX_t.2
        _ ≤ (ivLogB1.lo : ℝ) / (ivScale : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hleB) hD.le
        _ ≤ -(FFn (2 / 25) 1 - FFn' (2 / 25) 1) := mem_ivLogB1.1
    obtain ⟨hy0, hy1, hInR⟩ := hInR_mid (Real.exp (logXFn (3 / 100) M1Fn t)) hge_a hle_b
    have hval := hmid_pos hpos t ht
    refine ⟨Real.exp (-FFn (2 / 25) 1) / Real.exp (logXFn (3 / 100) M1Fn t), hy0, hy1, ?_, ?_⟩
    · rw [hX_eq_exp t ht]; exact hInR
    · rw [hX_eq_exp t ht, Real.log_exp, Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',
          Real.log_exp, Real.log_exp]
      linarith
  | 2 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbranch
    rcases hbranch with ⟨⟨⟨ht0_0, ht0_1, hleA, hpos⟩, hok_t0⟩, hok_t01⟩
    set tr : ℝ := (t0 : ℝ) / (ivScale : ℝ)
    have htr0 : 0 < tr := div_pos (by exact_mod_cast ht0_0) hD
    have htr1 : tr ≤ 1 := (div_le_one hD).2 (by exact_mod_cast ht0_1)
    have hFp08_t : (ivFp_pt 2 25 t0).Mem (FFn' (2 / 25) tr) := by
      simpa [tr] using mem_ivFp_pt (bn := 2) (bd := 25) (by norm_num) ht0_0 ht0_1 hok_t0 hok_t01
    have hF08_t : (ivF_pt 2 25 t0).Mem (FFn (2 / 25) tr) := by
      simpa [tr] using mem_ivF_pt (bn := 2) (bd := 25) (by norm_num) ht0_0 ht0_1 hok_t0 hok_t01
    have hlogBt_mem : (((Iv.ofScaled t0).mul (ivFp_pt 2 25 t0)).sub (ivF_pt 2 25 t0)).Mem
        (-(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr)) := by
      have heq : -(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr) = tr * FFn' (2 / 25) tr - FFn (2 / 25) tr := by ring
      rw [heq]
      exact Iv.mem_sub (Iv.mem_mul (mem_ofScaled t0) hFp08_t) hF08_t
    have hBpos : 0 < FFn (2 / 25) tr - tr * FFn' (2 / 25) tr := FFn_008_B_pos htr0 htr1
    intro t ht
    have hX_le_A : Real.exp (logXFn (3 / 100) M1Fn t) ≤ Real.exp (-FFn' (2 / 25) tr) := by
      apply Real.exp_le_exp.2
      calc logXFn (3 / 100) M1Fn t ≤ (logX.hi : ℝ) / (ivScale : ℝ) := (hlogX_mem t ht).2
        _ ≤ (-(ivFp_pt 2 25 t0).hi : ℝ) / (ivScale : ℝ) := by
            have : (logX.hi : ℝ) ≤ -((ivFp_pt 2 25 t0).hi : ℝ) := by exact_mod_cast hleA
            exact div_le_div_of_nonneg_right this hD.le
        _ = -(((ivFp_pt 2 25 t0).hi : ℝ) / (ivScale : ℝ)) := neg_div _ _
        _ ≤ -FFn' (2 / 25) tr := by linarith [hFp08_t.2]
    have hval := hconst_pos _ _ hlogBt_mem hpos t ht
    refine ⟨Real.exp (-(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr)),
      Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith), ?_, ?_⟩
    · rw [hX_eq_exp t ht]
      exact inR_mono (hInR_AB tr ⟨htr0, htr1⟩).1 (Real.exp_pos _) hX_le_A (Real.exp_pos _) le_rfl
    · rw [hX_eq_exp t ht, Real.log_exp, Real.log_exp]; linarith
  | 3 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbranch
    rcases hbranch with ⟨⟨⟨ht0_0, ht0_1, hleB, hpos⟩, hok_t0⟩, hok_t01⟩
    set tr : ℝ := (t0 : ℝ) / (ivScale : ℝ)
    have htr0 : 0 < tr := div_pos (by exact_mod_cast ht0_0) hD
    have htr1 : tr ≤ 1 := (div_le_one hD).2 (by exact_mod_cast ht0_1)
    have hFp08_t : (ivFp_pt 2 25 t0).Mem (FFn' (2 / 25) tr) := by
      simpa [tr] using mem_ivFp_pt (bn := 2) (bd := 25) (by norm_num) ht0_0 ht0_1 hok_t0 hok_t01
    have hF08_t : (ivF_pt 2 25 t0).Mem (FFn (2 / 25) tr) := by
      simpa [tr] using mem_ivF_pt (bn := 2) (bd := 25) (by norm_num) ht0_0 ht0_1 hok_t0 hok_t01
    have hlogBt_mem : (((Iv.ofScaled t0).mul (ivFp_pt 2 25 t0)).sub (ivF_pt 2 25 t0)).Mem
        (-(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr)) := by
      have heq : -(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr) = tr * FFn' (2 / 25) tr - FFn (2 / 25) tr := by ring
      rw [heq]
      exact Iv.mem_sub (Iv.mem_mul (mem_ofScaled t0) hFp08_t) hF08_t
    have hlogAt_mem : (ivFp_pt 2 25 t0).neg.Mem (-FFn' (2 / 25) tr) := Iv.mem_neg hFp08_t
    have hApos : 0 < FFn' (2 / 25) tr := FFn'_pos (by norm_num) (by norm_num) htr0 htr1
    intro t ht
    have hX_le_B : Real.exp (logXFn (3 / 100) M1Fn t) ≤ Real.exp (-(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr)) := by
      apply Real.exp_le_exp.2
      calc logXFn (3 / 100) M1Fn t ≤ (logX.hi : ℝ) / (ivScale : ℝ) := (hlogX_mem t ht).2
        _ ≤ ((((Iv.ofScaled t0).mul (ivFp_pt 2 25 t0)).sub (ivF_pt 2 25 t0)).lo : ℝ) / (ivScale : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hleB) hD.le
        _ ≤ -(FFn (2 / 25) tr - tr * FFn' (2 / 25) tr) := hlogBt_mem.1
    have hval := hconst_pos _ _ hlogAt_mem hpos t ht
    refine ⟨Real.exp (-FFn' (2 / 25) tr), Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith), ?_, ?_⟩
    · rw [hX_eq_exp t ht]
      exact inR_mono (hInR_AB tr ⟨htr0, htr1⟩).2 (Real.exp_pos _) hX_le_B (Real.exp_pos _) le_rfl
    · rw [hX_eq_exp t ht, Real.log_exp, Real.log_exp]; linarith
  | 4 =>
    simp only [decide_eq_true_eq] at hbranch
    rcases hbranch with ⟨hleB, hposMid, hposA⟩
    intro t ht
    have hle_b : Real.exp (logXFn (3 / 100) M1Fn t) ≤ Real.exp (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) := by
      apply Real.exp_le_exp.2
      calc logXFn (3 / 100) M1Fn t ≤ (logX.hi : ℝ) / (ivScale : ℝ) := (hlogX_mem t ht).2
        _ ≤ (ivLogB1.lo : ℝ) / (ivScale : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hleB) hD.le
        _ ≤ -(FFn (2 / 25) 1 - FFn' (2 / 25) 1) := mem_ivLogB1.1
    by_cases hX_le_A1 : Real.exp (logXFn (3 / 100) M1Fn t) ≤ Real.exp (-FFn' (2 / 25) 1)
    · have hB1pos : 0 < FFn (2 / 25) 1 - 1 * FFn' (2 / 25) 1 := FFn_008_B_pos zero_lt_one le_rfl
      have hval := hconst_pos ivLogB1 (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) mem_ivLogB1 hposA t ht
      refine ⟨Real.exp (-(FFn (2 / 25) 1 - 1 * FFn' (2 / 25) 1)),
        Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith), ?_, ?_⟩
      · rw [hX_eq_exp t ht]
        exact inR_mono (hInR_AB 1 ⟨zero_lt_one, le_rfl⟩).1 (Real.exp_pos _) hX_le_A1 (Real.exp_pos _) le_rfl
      · rw [hX_eq_exp t ht, Real.log_exp, Real.log_exp, one_mul]; linarith
    · have hge_a : Real.exp (-FFn' (2 / 25) 1) ≤ Real.exp (logXFn (3 / 100) M1Fn t) := le_of_not_ge hX_le_A1
      obtain ⟨hy0, hy1, hInR⟩ := hInR_mid (Real.exp (logXFn (3 / 100) M1Fn t)) hge_a hle_b
      have hval := hmid_pos hposMid t ht
      refine ⟨Real.exp (-FFn (2 / 25) 1) / Real.exp (logXFn (3 / 100) M1Fn t), hy0, hy1, ?_, ?_⟩
      · rw [hX_eq_exp t ht]; exact hInR
      · rw [hX_eq_exp t ht, Real.log_exp, Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',
            Real.log_exp, Real.log_exp]
        linarith
  | _ + 5 => simp at hbranch

/- ### Contiguous cover checker and induction -/

def coverOk {α : Type} (bounds : α → ℤ × ℤ) (check : α → Bool) (cur target : ℤ) : List α → Bool
  | [] => false
  | [e] =>
    let (lo, hi) := bounds e
    decide (lo = cur ∧ lo ≤ hi ∧ hi = target) && check e
  | e :: rest =>
    let (lo, hi) := bounds e
    decide (lo = cur ∧ lo ≤ hi) && check e && coverOk bounds check hi target rest

lemma coverOk_sound {α : Type} {bounds : α → ℤ × ℤ} {check : α → Bool} {P : ℝ → Prop}
    (hsound : ∀ e, check e = true →
      ∀ t ∈ Icc (((bounds e).1 : ℝ) / (ivScale : ℝ)) (((bounds e).2 : ℝ) / (ivScale : ℝ)), P t) :
    ∀ (L : List α) (cur target : ℤ), coverOk bounds check cur target L = true →
      ∀ t ∈ Icc ((cur : ℝ) / (ivScale : ℝ)) ((target : ℝ) / (ivScale : ℝ)), P t := by
  intro L
  induction L with
  | nil => intro cur target hok; simp [coverOk] at hok
  | cons e rest ih =>
    cases rest with
    | nil =>
      intro cur target hok t ht
      unfold coverOk at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨hlo, _, hhi⟩, hchk⟩
      rw [← hlo, ← hhi] at ht
      exact hsound e hchk t ht
    | cons e2 rest2 =>
      intro cur target hok t ht
      unfold coverOk at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨⟨hlo, _⟩, hchk⟩, hrest⟩
      by_cases hle : t ≤ (((bounds e).2 : ℝ) / (ivScale : ℝ))
      · rw [← hlo] at ht
        exact hsound e hchk t ⟨ht.1, hle⟩
      · exact ih (bounds e).2 target hrest t ⟨le_of_not_ge hle, ht.2⟩

/- ### Verified certificate tables covering [1/250, 1] -/

def certPhi0 : List (ℤ × ℤ) := [
  (4000000, 4486328), (4486328, 4972656), (4972656, 5458984), (5458984, 5945312),
  (5945312, 6431640), (6431640, 6917968), (6917968, 7890625), (7890625, 8863281),
  (8863281, 9835937), (9835937, 10808593), (10808593, 11781250), (11781250, 12753906),
  (12753906, 13726562), (13726562, 15671875), (15671875, 17617187), (17617187, 19562500),
  (19562500, 21507812), (21507812, 23453125), (23453125, 25398437), (25398437, 27343750),
  (27343750, 31234375), (31234375, 35125000), (35125000, 39015625), (39015625, 42906250),
  (42906250, 46796875), (46796875, 50687500), (50687500, 54578125), (54578125, 58468750),
  (58468750, 66250000), (66250000, 74031250), (74031250, 81812500), (81812500, 89593750),
  (89593750, 97375000), (97375000, 105156250), (105156250, 112937500), (112937500, 120718750),
  (120718750, 128500000), (128500000, 136281250), (136281250, 144062500), (144062500, 159625000),
  (159625000, 175187500), (175187500, 190750000), (190750000, 206312500), (206312500, 221875000),
  (221875000, 237437500), (237437500, 253000000), (253000000, 268562500), (268562500, 284125000),
  (284125000, 299687500), (299687500, 315250000), (315250000, 330812500), (330812500, 346375000),
  (346375000, 361937500), (361937500, 377500000), (377500000, 393062500), (393062500, 408625000),
  (408625000, 424187500), (424187500, 439750000), (439750000, 455312500), (455312500, 470875000),
  (470875000, 486437500), (486437500, 502000000), (502000000, 533125000), (533125000, 564250000),
  (564250000, 595375000), (595375000, 626500000), (626500000, 657625000), (657625000, 688750000),
  (688750000, 751000000), (751000000, 813250000), (813250000, 875500000), (875500000, 937750000),
  (937750000, 1000000000)
]

def certPhi1_0 : List (ℤ × ℤ × ℕ × ℤ) := [
  (4000000, 4486328, 0, 0), (4486328, 4972656, 0, 0), (4972656, 5945312, 3, 11338481),
  (5945312, 6917968, 3, 13626129), (6917968, 7890625, 3, 15916531), (7890625, 8863281, 0, 0),
  (8863281, 9835937, 0, 0), (9835937, 11781250, 3, 22625584), (11781250, 13726562, 3, 27295060),
  (13726562, 15671875, 3, 31987701), (15671875, 17617187, 0, 0), (17617187, 19562500, 0, 0),
  (19562500, 23453125, 3, 45826698), (23453125, 27343750, 3, 55558674), (27343750, 31234375, 3, 65416507),
  (31234375, 35125000, 3, 75412621), (35125000, 42906250, 3, 84538117), (42906250, 50687500, 3, 105436530),
  (50687500, 58468750, 3, 126946848), (58468750, 66250000, 3, 149126569), (66250000, 74031250, 3, 172022694),
  (74031250, 81812500, 3, 195677537), (81812500, 89593750, 0, 0), (89593750, 97375000, 0, 0),
  (97375000, 112937500, 3, 269430684), (112937500, 128500000, 3, 324622008), (128500000, 144062500, 3, 383640326),
  (144062500, 159625000, 3, 446656558), (159625000, 175187500, 3, 513706131), (175187500, 190750000, 3, 584639115),
  (190750000, 206312500, 3, 659082338), (206312500, 221875000, 3, 736434894), (221875000, 237437500, 3, 815912032),
  (237437500, 245218750, 3, 898387929), (245218750, 253000000, 3, 938912084), (253000000, 260781250, 3, 979425852),
  (260781250, 268562500, 1, 0), (268562500, 284125000, 1, 0), (284125000, 299687500, 1, 0),
  (299687500, 307468750, 1, 0), (307468750, 315250000, 1, 0), (315250000, 323031250, 1, 0),
  (323031250, 326921875, 1, 0), (326921875, 330812500, 1, 0), (330812500, 334703125, 1, 0),
  (334703125, 338593750, 1, 0), (338593750, 342484375, 1, 0), (342484375, 346375000, 1, 0),
  (346375000, 350265625, 1, 0), (350265625, 354156250, 1, 0), (354156250, 358046875, 1, 0),
  (358046875, 359992187, 4, 0), (359992187, 360964843, 2, 997410658), (360964843, 361937500, 2, 992769635),
  (361937500, 362910156, 2, 988155228), (362910156, 363882812, 2, 983567363), (363882812, 364855468, 2, 979006011),
  (364855468, 365828125, 2, 974471189), (365828125, 366800781, 2, 969962653), (366800781, 367773437, 2, 965480519),
  (367773437, 368746093, 2, 961024653), (368746093, 369718750, 2, 956595007), (369718750, 371664062, 2, 952210922),
  (371664062, 373609375, 2, 943481917), (373609375, 375554687, 2, 934856692), (375554687, 377500000, 2, 926334734),
  (377500000, 379445312, 2, 917915407), (379445312, 381390625, 2, 909598177), (381390625, 383335937, 2, 901382250),
  (383335937, 385281250, 2, 893267106)
]

def certPhi1_1 : List (ℤ × ℤ × ℕ × ℤ) := [
  (385281250, 387226562, 2, 885251909), (387226562, 389171875, 2, 877336042), (389171875, 391117187, 2, 869518709),
  (391117187, 393062500, 2, 861799164), (393062500, 395007812, 2, 854176575), (395007812, 396953125, 2, 846650190),
  (396953125, 398898437, 2, 839219133), (398898437, 400843750, 2, 831882566), (400843750, 402789062, 2, 824639643),
  (402789062, 404734375, 2, 817489513), (404734375, 408625000, 2, 810492071), (408625000, 412515625, 2, 796645808),
  (412515625, 416406250, 2, 783155937), (416406250, 420296875, 2, 770015030), (420296875, 424187500, 2, 757215278),
  (424187500, 428078125, 2, 744748907), (428078125, 431968750, 2, 732608065), (431968750, 435859375, 2, 720784821),
  (435859375, 439750000, 2, 709271244), (439750000, 443640625, 2, 698059442), (443640625, 447531250, 2, 687141543),
  (447531250, 451421875, 2, 676509730), (451421875, 455312500, 2, 666156314), (455312500, 459203125, 2, 656073639),
  (459203125, 463093750, 2, 646254151), (463093750, 466984375, 2, 636690508), (466984375, 470875000, 2, 627375407),
  (470875000, 474765625, 2, 618301730), (474765625, 478656250, 2, 609462506), (478656250, 482546875, 2, 600850978),
  (482546875, 486437500, 2, 592460421), (486437500, 490328125, 2, 584284421), (490328125, 494218750, 2, 576316630),
  (494218750, 498109375, 2, 568550915), (498109375, 502000000, 2, 560981342), (502000000, 505890625, 2, 553602054),
  (505890625, 509781250, 2, 546407498), (509781250, 513671875, 2, 539392153), (513671875, 517562500, 2, 532550727),
  (517562500, 521453125, 2, 525878179), (521453125, 525343750, 2, 519369436), (525343750, 527289062, 2, 512993239),
  (527289062, 529234375, 2, 509876900), (529234375, 531179687, 2, 506798586), (531179687, 533125000, 2, 503757751),
  (533125000, 535070312, 2, 500753782), (535070312, 537015625, 2, 497786229), (537015625, 538960937, 2, 494854517),
  (538960937, 540906250, 2, 491958127), (540906250, 542851562, 2, 489096548), (542851562, 544796875, 2, 486269270),
  (544796875, 546742187, 2, 483475841), (546742187, 548687500, 2, 480715688), (548687500, 550632812, 2, 477988389),
  (550632812, 552578125, 2, 475293477), (552578125, 554523437, 2, 472630472), (554523437, 556468750, 2, 469998922),
  (556468750, 558414062, 2, 467398376), (558414062, 560359375, 2, 464828404), (560359375, 562304687, 2, 462288554),
  (562304687, 564250000, 2, 459778421), (564250000, 566195312, 2, 457297569), (566195312, 568140625, 2, 454845607),
  (568140625, 570085937, 2, 452422147), (570085937, 572031250, 2, 450026723), (572031250, 573976562, 2, 447658994),
  (573976562, 575921875, 2, 445318612), (575921875, 577867187, 2, 443005121), (577867187, 579812500, 2, 440718194),
  (579812500, 581757812, 2, 438457465)
]

def certPhi1_2 : List (ℤ × ℤ × ℕ × ℤ) := [
  (581757812, 583703125, 2, 436222570), (583703125, 585648437, 2, 434013167), (585648437, 587593750, 2, 431828890),
  (587593750, 589539062, 2, 429669417), (589539062, 590511718, 2, 427529880), (590511718, 591484375, 2, 426471463),
  (591484375, 592457031, 2, 425419041), (592457031, 593429687, 2, 424372568), (593429687, 594402343, 2, 423332010),
  (594402343, 595375000, 2, 422297322), (595375000, 596347656, 2, 421268480), (596347656, 597320312, 2, 420245414),
  (597320312, 598292968, 2, 419228112), (598292968, 599265625, 2, 418216541), (599265625, 600238281, 2, 417210632),
  (600238281, 601210937, 2, 416210366), (601210937, 602183593, 2, 415215726), (602183593, 603156250, 2, 414226642),
  (603156250, 604128906, 2, 413243076), (604128906, 605101562, 2, 412265028), (605101562, 606074218, 2, 411292407),
  (606074218, 607046875, 2, 410325237), (607046875, 608019531, 2, 409363446), (608019531, 608992187, 2, 408407014),
  (608992187, 609964843, 2, 407455891), (609964843, 610937500, 2, 406510048), (610937500, 611910156, 2, 405569456),
  (611910156, 612882812, 2, 404634093), (612882812, 613855468, 2, 403703902), (613855468, 614828125, 2, 402778838),
  (614828125, 615800781, 2, 401858900), (615800781, 616773437, 2, 400944064), (616773437, 617746093, 2, 400034263),
  (617746093, 618718750, 2, 399129475), (618718750, 619691406, 2, 398229674), (619691406, 620664062, 2, 397334815),
  (620664062, 621636718, 2, 396444892), (621636718, 622609375, 2, 395559861), (622609375, 623582031, 2, 394679683),
  (623582031, 624554687, 2, 393804328), (624554687, 625527343, 2, 392933766), (625527343, 626500000, 2, 392067995),
  (626500000, 627472656, 2, 391206934), (627472656, 628445312, 2, 390350593), (628445312, 629417968, 2, 389498917),
  (629417968, 630390625, 2, 388651907), (630390625, 631363281, 2, 387809516), (631363281, 632335937, 2, 386971707),
  (632335937, 633308593, 2, 386138463), (633308593, 634281250, 2, 385309736), (634281250, 635253906, 2, 384485539),
  (635253906, 636226562, 2, 383665814), (636226562, 637199218, 2, 382850528), (637199218, 638171875, 2, 382039672),
  (638171875, 639144531, 2, 381233208), (639144531, 640117187, 2, 380431106), (640117187, 641089843, 2, 379633364),
  (641089843, 642062500, 2, 378839917), (642062500, 643035156, 2, 378050776), (643035156, 644007812, 2, 377265887),
  (644007812, 644980468, 2, 376485219), (644980468, 645953125, 2, 375708776), (645953125, 646925781, 2, 374936525),
  (646925781, 647898437, 2, 374168435), (647898437, 648871093, 2, 373404457), (648871093, 649843750, 2, 372644625),
  (649843750, 650816406, 2, 371888851), (650816406, 651789062, 2, 371137129), (651789062, 652761718, 2, 370389466),
  (652761718, 653734375, 2, 369645790)
]

def certPhi1_3 : List (ℤ × ℤ × ℕ × ℤ) := [
  (653734375, 654707031, 2, 368906122), (654707031, 655679687, 2, 368170404), (655679687, 656652343, 2, 367438640),
  (656652343, 657625000, 2, 366710785), (657625000, 658597656, 2, 365986809), (658597656, 659570312, 2, 365266743),
  (659570312, 660542968, 2, 364550496), (660542968, 661515625, 2, 363838092), (661515625, 662488281, 2, 363129462),
  (662488281, 663460937, 2, 362424634), (663460937, 664433593, 2, 361723544), (664433593, 665406250, 2, 361026213),
  (665406250, 666378906, 2, 360332590), (666378906, 667351562, 2, 359642653), (667351562, 668324218, 2, 358956378),
  (668324218, 669296875, 2, 358273775), (669296875, 671242187, 2, 357597797), (671242187, 673187500, 2, 356250593),
  (673187500, 675132812, 2, 354917646), (675132812, 677078125, 2, 353598835), (677078125, 679023437, 2, 352293945),
  (679023437, 680968750, 2, 351002831), (680968750, 682914062, 2, 349725352), (682914062, 684859375, 2, 348461340),
  (684859375, 686804687, 2, 347210666), (686804687, 688750000, 2, 345973135), (688750000, 690695312, 2, 344748655),
  (690695312, 692640625, 2, 343537042), (692640625, 694585937, 2, 342338170), (694585937, 696531250, 2, 341151888),
  (696531250, 698476562, 2, 339978073), (698476562, 700421875, 2, 338816585), (700421875, 702367187, 2, 337667272),
  (702367187, 704312500, 2, 336530015), (704312500, 708203125, 2, 335414873), (708203125, 712093750, 2, 333199285),
  (712093750, 715984375, 2, 331029894), (715984375, 719875000, 2, 328905701), (719875000, 723765625, 2, 326825774),
  (723765625, 727656250, 2, 324789179), (727656250, 731546875, 2, 322795007), (731546875, 735437500, 2, 320842397),
  (735437500, 739328125, 2, 318930511), (739328125, 743218750, 2, 317058517), (743218750, 751000000, 2, 315259963),
  (751000000, 758781250, 2, 311707153), (758781250, 766562500, 2, 308301671), (766562500, 774343750, 2, 305037812),
  (774343750, 782125000, 2, 301910180), (782125000, 789906250, 2, 298913681), (789906250, 797687500, 2, 296043466),
  (797687500, 813250000, 2, 293404741), (813250000, 828812500, 2, 288248681), (828812500, 844375000, 2, 283530001),
  (844375000, 859937500, 2, 279219181), (859937500, 875500000, 2, 275293901), (875500000, 891062500, 2, 271727302),
  (891062500, 906625000, 2, 268494492), (906625000, 922187500, 2, 265575002), (922187500, 937750000, 2, 262950086),
  (937750000, 953312500, 2, 260602450), (953312500, 968875000, 2, 258516221), (968875000, 984437500, 2, 256676656),
  (984437500, 1000000000, 2, 255070148)
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma certPhi0_ok : coverOk id (fun p => checkPhi0Iv p.1 p.2) 4000000 1000000000 certPhi0 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma certPhi1_0_ok : coverOk (fun e => (e.1, e.2.1)) checkPhi1Iv 4000000 385281250 certPhi1_0 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma certPhi1_1_ok : coverOk (fun e => (e.1, e.2.1)) checkPhi1Iv 385281250 581757812 certPhi1_1 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma certPhi1_2_ok : coverOk (fun e => (e.1, e.2.1)) checkPhi1Iv 581757812 653734375 certPhi1_2 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma certPhi1_3_ok : coverOk (fun e => (e.1, e.2.1)) checkPhi1Iv 653734375 1000000000 certPhi1_3 = true := by
  decide

/-- Full GNNW numerical condition for F_{0.08} with M_0 on (0, 1]. -/
theorem phi0_cond :
    ∀ t ∈ Ioc (0 : ℝ) 1, ∃ y : ℝ, 0 < y ∧ y < 1 ∧
      let X := (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t)
      InR X y ∧
      -(Real.log X + t * Real.log (M0Fn t) + t * Real.log y) / 2 < FFn (2 / 25) t := by
  intro t ht
  by_cases hsmall : t ≤ 1 / 250
  · have hm_lo : t * Real.exp (-t) ≤ M0Fn t := le_rfl
    have hm_hi : M0Fn t ≤ t := by
      unfold M0Fn
      calc t * Real.exp (-t) ≤ t * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by linarith [ht.1])) ht.1.le
        _ = t := mul_one _
    obtain ⟨hX0, hX1, hphi⟩ := small_t_phi_pos (b := 2 / 25) (by norm_num) (by norm_num) ht.1 hsmall hm_lo hm_hi
    set X := (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t)
    exact ⟨1 - X, sub_pos.2 hX1, by linarith, inR_es hX0 hX1, hphi⟩
  · have ht_ge : (4000000 : ℝ) / (ivScale : ℝ) ≤ t := by
      have : (4000000 : ℝ) / (ivScale : ℝ) = 1 / 250 := by unfold ivScale; norm_num
      linarith
    have ht_le : t ≤ (1000000000 : ℝ) / (ivScale : ℝ) := by
      have : (1000000000 : ℝ) / (ivScale : ℝ) = 1 := by unfold ivScale; norm_num
      linarith [ht.2]
    have hcov := coverOk_sound (bounds := id) (check := fun p : ℤ × ℤ => checkPhi0Iv p.1 p.2)
      (P := fun s =>
        let X := (1 - Real.exp (-FFn' (2 / 25) s)) ^ (1 / (1 - M0Fn s)) * (1 - M0Fn s)
        0 < X ∧ X < 1 ∧ -(Real.log X + s * Real.log (M0Fn s) + s * Real.log (1 - X)) / 2 < FFn (2 / 25) s)
      (fun p hp => checkPhi0Iv_sound hp) certPhi0 4000000 1000000000 certPhi0_ok t ⟨ht_ge, ht_le⟩
    rcases hcov with ⟨hX0, hX1, hphi⟩
    set X := (1 - Real.exp (-FFn' (2 / 25) t)) ^ (1 / (1 - M0Fn t)) * (1 - M0Fn t)
    exact ⟨1 - X, sub_pos.2 hX1, by linarith, inR_es hX0 hX1, hphi⟩

/-- Full GNNW numerical condition for F_{0.03} with M_1 on (0, 1], given the frontier of F_{0.08}. -/
theorem phi1_cond
    (hInR_AB : ∀ t ∈ Ioc (0 : ℝ) 1,
      InR (Real.exp (-FFn' (2 / 25) t)) (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) ∧
      InR (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) (Real.exp (-FFn' (2 / 25) t)))
    (hInR_mid : ∀ x : ℝ,
      Real.exp (-FFn' (2 / 25) 1) ≤ x → x ≤ Real.exp (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) →
      0 < Real.exp (-FFn (2 / 25) 1) / x ∧ Real.exp (-FFn (2 / 25) 1) / x < 1 ∧
      InR x (Real.exp (-FFn (2 / 25) 1) / x)) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ∃ y : ℝ, 0 < y ∧ y < 1 ∧
      let X := (1 - Real.exp (-FFn' (3 / 100) t)) ^ (1 / (1 - M1Fn t)) * (1 - M1Fn t)
      InR X y ∧
      -(Real.log X + t * Real.log (M1Fn t) + t * Real.log y) / 2 < FFn (3 / 100) t := by
  intro t ht
  by_cases hsmall : t ≤ 1 / 250
  · have hm_lo : t * Real.exp (-t) ≤ M1Fn t := by
      unfold M1Fn
      apply mul_le_mul_of_nonneg_left _ ht.1.le
      apply Real.exp_le_exp.2
      nlinarith [ht.1]
    have hm_hi : M1Fn t ≤ t := by
      unfold M1Fn
      have hexp : Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      calc t * Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2) ≤ t * 1 := mul_le_mul_of_nonneg_left hexp ht.1.le
        _ = t := mul_one _
    obtain ⟨hX0, hX1, hphi⟩ := small_t_phi_pos (b := 3 / 100) (by norm_num) (by norm_num) ht.1 hsmall hm_lo hm_hi
    set X := (1 - Real.exp (-FFn' (3 / 100) t)) ^ (1 / (1 - M1Fn t)) * (1 - M1Fn t)
    exact ⟨1 - X, sub_pos.2 hX1, by linarith, inR_es hX0 hX1, hphi⟩
  · have ht_ge : (4000000 : ℝ) / (ivScale : ℝ) ≤ t := by
      have : (4000000 : ℝ) / (ivScale : ℝ) = 1 / 250 := by unfold ivScale; norm_num
      linarith
    have ht_le : t ≤ (1000000000 : ℝ) / (ivScale : ℝ) := by
      have : (1000000000 : ℝ) / (ivScale : ℝ) = 1 := by unfold ivScale; norm_num
      linarith [ht.2]
    have hsound := fun e he => checkPhi1Iv_sound hInR_AB hInR_mid (e := e) he
    by_cases h1 : t ≤ (385281250 : ℝ) / (ivScale : ℝ)
    · exact coverOk_sound hsound certPhi1_0 4000000 385281250 certPhi1_0_ok t ⟨ht_ge, h1⟩
    · by_cases h2 : t ≤ (581757812 : ℝ) / (ivScale : ℝ)
      · exact coverOk_sound hsound certPhi1_1 385281250 581757812 certPhi1_1_ok t ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : t ≤ (653734375 : ℝ) / (ivScale : ℝ)
        · exact coverOk_sound hsound certPhi1_2 581757812 653734375 certPhi1_2_ok t ⟨le_of_not_ge h2, h3⟩
        · exact coverOk_sound hsound certPhi1_3 653734375 1000000000 certPhi1_3_ok t ⟨le_of_not_ge h3, ht_le⟩

end Erdos627AFM

/- ==================== Section: Main.lean ====================-/
/- Main theorem proving the Erdős 627 AFM upper bound H1. -/

namespace Erdos627AFM

open SimpleGraph Real Set Filter

/-- Base Ramsey upper bound with F_{0.08} (GNNW Theorem 14 first iteration). -/
theorem ramsey_F008 :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((FFn (2 / 25) ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by
  apply general_ramsey_bound (FFn (2 / 25)) (FFn' (2 / 25)) M0Fn
  · intro t ht; exact hasDerivAt_FFn (2 / 25) ht.1
  · intro t ht; exact (hasDerivAt_FFn' (2 / 25) ht.1).continuousAt.continuousWithinAt
  · intro t ht; exact FFn_pos (by norm_num) (by norm_num) ht.1 ht.2
  · intro t ht; exact FFn'_pos (by norm_num) (by norm_num) ht.1 ht.2
  · intro t _; exact (hasDerivAt_M0Fn t).continuousAt.continuousWithinAt
  · intro t ht
    refine ⟨mul_pos ht.1 (Real.exp_pos _), ?_⟩
    unfold M0Fn
    have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith [ht.1])
    calc t * Real.exp (-t) ≤ 1 * Real.exp (-t) := mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos _).le
      _ < 1 := by linarith
  · exact phi0_cond

/-- Iterated Ramsey upper bound with F_{0.03} (GNNW Theorem 1 / second iteration). -/
theorem ramsey_F003 :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramsey k l : ℝ) ≤ Real.exp ((FFn (3 / 100) ((l : ℝ) / (k : ℝ)) + ε) * (k : ℝ)) := by
  have hF08_deriv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt (FFn (2 / 25)) (FFn' (2 / 25) t) t :=
    fun t ht => hasDerivAt_FFn (2 / 25) ht.1
  have hF08_anti : AntitoneOn (FFn' (2 / 25)) (Ioc (0 : ℝ) 1) :=
    FFn'_anti (by norm_num) (by norm_num)
  have hF08_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < FFn' (2 / 25) t :=
    fun t ht => FFn'_pos (by norm_num) (by norm_num) ht.1 ht.2
  have hInR_AB : ∀ t ∈ Ioc (0 : ℝ) 1,
      InR (Real.exp (-FFn' (2 / 25) t)) (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) ∧
      InR (Real.exp (-(FFn (2 / 25) t - t * FFn' (2 / 25) t))) (Real.exp (-FFn' (2 / 25) t)) :=
    fun t ht => frontier_AB (FFn (2 / 25)) (FFn' (2 / 25)) hF08_deriv hF08_anti hF08_pos ramsey_F008
      ht.1 ht.2 (FFn_008_B_pos ht.1 ht.2) (FFn_008_AB_le ht.1 ht.2)
  have hInR_mid : ∀ x : ℝ,
      Real.exp (-FFn' (2 / 25) 1) ≤ x → x ≤ Real.exp (-(FFn (2 / 25) 1 - FFn' (2 / 25) 1)) →
      0 < Real.exp (-FFn (2 / 25) 1) / x ∧ Real.exp (-FFn (2 / 25) 1) / x < 1 ∧
      InR x (Real.exp (-FFn (2 / 25) 1) / x) :=
    fun x hxa hxb => frontier_mid (FFn (2 / 25)) (FFn' (2 / 25)) hF08_deriv hF08_anti hF08_pos ramsey_F008
      (by simpa using FFn_008_B_pos zero_lt_one le_rfl) hxa hxb
  apply general_ramsey_bound (FFn (3 / 100)) (FFn' (3 / 100)) M1Fn
  · intro t ht; exact hasDerivAt_FFn (3 / 100) ht.1
  · intro t ht; exact (hasDerivAt_FFn' (3 / 100) ht.1).continuousAt.continuousWithinAt
  · intro t ht; exact FFn_pos (by norm_num) (by norm_num) ht.1 ht.2
  · intro t ht; exact FFn'_pos (by norm_num) (by norm_num) ht.1 ht.2
  · intro t _; exact (hasDerivAt_M1Fn t).continuousAt.continuousWithinAt
  · intro t ht
    refine ⟨mul_pos ht.1 (Real.exp_pos _), ?_⟩
    unfold M1Fn
    have he : Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [ht.1])
    calc t * Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2)
        ≤ 1 * Real.exp (-(2 / 3) * t - (3 / 10) * t ^ 2) :=
          mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos _).le
      _ < 1 := by linarith
  · exact phi1_cond hInR_AB hInR_mid

/-- Algebraic relation between `Real.binEntropy (a / (a + b))` and `hEntN (a / b)`. -/
lemma binEntropy_eq_div_mul_hEntN {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.binEntropy (a / (a + b)) = b * hEntN (a / b) := by
  have hab : 0 < a + b := by positivity
  have h1 : 1 - a / (a + b) = b / (a + b) := by field_simp [hab.ne']; ring
  have h2 : 1 + a / b = (a + b) / b := by field_simp [hb.ne']; ring
  unfold Real.binEntropy hEntN
  rw [h1, h2, Real.log_inv, Real.log_inv, Real.log_div ha.ne' hab.ne', Real.log_div hb.ne' hab.ne',
      Real.log_div hab.ne' hb.ne', Real.log_div ha.ne' hb.ne']
  field_simp [hab.ne', hb.ne']
  ring

/-- Small-ratio upper bound: for `0 < lam ≤ 1`, `hEntN lam ≤ 6 * lam ^ (3 / 4)`. -/
lemma hEntN_le_six_rpow {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    hEntN lam ≤ 6 * lam ^ ((3 : ℝ) / 4) := by
  unfold hEntN
  have hlog1 : Real.log (1 + lam) ≤ lam := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + lam by linarith)]
  have h1t : (1 + lam) * Real.log (1 + lam) ≤ 2 * lam := by
    have hlog_nn : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
    nlinarith
  have hlog_inv : -Real.log lam ≤ 4 * lam ^ (-(1 : ℝ) / 4) := by
    have hpow_pos : 0 < lam ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos h0 _
    have hstep := Real.log_le_sub_one_of_pos hpow_pos
    rw [Real.log_rpow h0] at hstep
    linarith
  have hneg : -lam * Real.log lam ≤ 4 * lam ^ ((3 : ℝ) / 4) := by
    calc -lam * Real.log lam = lam * (-Real.log lam) := by ring
      _ ≤ lam * (4 * lam ^ (-(1 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hlog_inv h0.le
      _ = 4 * (lam ^ (1 : ℝ) * lam ^ (-(1 : ℝ) / 4)) := by rw [Real.rpow_one]; ring
      _ = 4 * lam ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_add h0]; norm_num
  have hlam_le : lam ≤ lam ^ ((3 : ℝ) / 4) := by
    have := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  linarith

set_option maxHeartbeats 800000 in
/-- Core graph-level bound for `a = H.cliqueNum ≤ H.indepNum = b`. -/
lemma h1_wlog_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ K0 : ℕ, ∀ k : ℕ, K0 ≤ k → ∀ H : SimpleGraph (Fin k),
      H.cliqueNum ≤ H.indepNum →
      let a : ℝ := H.cliqueNum
      let b : ℝ := H.indepNum
      let x := min a b / (a + b)
      (Real.logb 2 k) ^ 2 ≤
        (((Real.binEntropy x - (0.14 / Real.exp 1) * x) /
          (Real.log 2 * Real.sqrt (x * (1 - x)))) ^ 2 + δ) * (a * b) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Choose small-ratio cutoff lam₀ ∈ (0, 1/2]
  let lam₀ : ℝ := min (1 / 2) ((δ * (Real.log 2) ^ 2 / 36) ^ 2)
  have hlam₀_pos : 0 < lam₀ := by dsimp [lam₀]; positivity
  have hlam₀_le : lam₀ ≤ 1 / 2 := min_le_left _ _
  have hlam₀_sq : lam₀ ≤ (δ * (Real.log 2) ^ 2 / 36) ^ 2 := min_le_right _ _
  -- Choose ε > 0 for Case 2 (lam₀ < lam ≤ 1)
  let ε : ℝ := min 1 (δ * lam₀ * (Real.log 2) ^ 2 / 12)
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hε_le1 : ε ≤ 1 := min_le_left _ _
  have hε_bd : 12 * ε ≤ δ * lam₀ * (Real.log 2) ^ 2 := by
    have : ε ≤ δ * lam₀ * (Real.log 2) ^ 2 / 12 := min_le_right _ _
    linarith
  obtain ⟨K_ram, hK_ram⟩ := ramsey_F003 ε hε_pos
  -- Choose B0 large enough that b ≥ B0 handles both K_ram and shift (a+1)/(b+1)
  let C_shift : ℝ := FFn (3 / 100) 1 + 2 * FFn' (3 / 100) lam₀ + ε
  obtain ⟨B1, hB1⟩ := exists_nat_gt (C_shift / ε)
  let B0 : ℕ := max (max K_ram B1) 2
  -- Since k ≤ 4^b whenever H.cliqueNum ≤ H.indepNum = b, taking K0 = 4^B0 + 1 forces b ≥ B0!
  refine ⟨4 ^ B0 + 1, fun k hk H hle => ?_⟩
  have hk1 : 1 ≤ k := by
    have : 1 ≤ 4 ^ B0 := Nat.one_le_pow B0 4 (by norm_num)
    omega
  -- Establish 1 ≤ H.cliqueNum and 1 ≤ H.indepNum
  have ha1_nat : 1 ≤ H.cliqueNum := by
    let v : Fin k := ⟨0, by omega⟩
    have hc : H.IsClique ({v} : Finset (Fin k)) := by simp [SimpleGraph.isClique_iff]
    simpa using hc.card_le_cliqueNum
  have hb1_nat : 1 ≤ H.indepNum := ha1_nat.trans hle
  set an : ℕ := H.cliqueNum
  set bn : ℕ := H.indepNum
  set a : ℝ := (an : ℝ)
  set b : ℝ := (bn : ℝ)
  have ha0 : 0 < a := Nat.cast_pos.2 (by omega)
  have hb0 : 0 < b := Nat.cast_pos.2 (by omega)
  have hab_le : a ≤ b := Nat.cast_le.2 hle
  have hab_pos : 0 < a + b := by positivity
  -- Key Ramsey and Erdős-Szekeres bounds on k
  have hk_lt_R : k < ramsey (bn + 1) (an + 1) := by
    rw [ramsey_symm]
    exact lt_ramsey_of_cliqueNum_indepNum H
  have hk_le_choose : k ≤ Nat.choose (an + bn) an := by
    have h1 := ramsey_le_choose (by omega : 1 ≤ an + 1) (by omega : 1 ≤ bn + 1)
    have h2 : an + 1 + (bn + 1) - 2 = an + bn := by omega
    have h3 : an + 1 - 1 = an := by omega
    rw [h2, h3] at h1
    rw [ramsey_symm] at hk_lt_R
    exact hk_lt_R.le.trans h1
  -- Deduce B0 ≤ bn from k > 4^B0 and k ≤ choose(an + bn, an) ≤ 2^(2*bn) = 4^bn
  have hbn_ge : B0 ≤ bn := by
    have hk_le_4 : k ≤ 4 ^ bn := by
      calc k ≤ Nat.choose (an + bn) an := hk_le_choose
        _ ≤ 2 ^ (an + bn) := Nat.choose_le_two_pow (an + bn) an
        _ ≤ 2 ^ (2 * bn) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 ^ bn := by rw [pow_mul]; norm_num
    by_contra hlt
    have hbn_lt : bn < B0 := lt_of_not_ge hlt
    have : 4 ^ bn ≤ 4 ^ B0 := Nat.pow_le_pow_right (by norm_num) hbn_lt.le
    omega
  -- Simplify min a b / (a + b) = a / (a + b)
  set x : ℝ := a / (a + b)
  set lam : ℝ := a / b
  have hmin_eq : min a b / (a + b) = x := by rw [min_eq_left hab_le]
  dsimp only
  rw [hmin_eq]
  have hlam0 : 0 < lam := div_pos ha0 hb0
  have hlam1 : lam ≤ 1 := (div_le_one hb0).2 hab_le
  have h1mx : 1 - x = b / (a + b) := by dsimp [x]; field_simp [hab_pos.ne']; ring
  have hx1mx : x * (1 - x) = a * b / (a + b) ^ 2 := by
    rw [h1mx]; dsimp [x]; rw [div_mul_div_comm, ← sq]
  have hsqrt : Real.sqrt (x * (1 - x)) = Real.sqrt (a * b) / (a + b) := by
    rw [hx1mx, Real.sqrt_div (by positivity), Real.sqrt_sq hab_pos.le]
  have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlogb_eq : Real.logb 2 (k : ℝ) = Real.log (k : ℝ) / Real.log 2 := rfl
  -- Split into small ratio (lam ≤ lam₀) vs main ratio (lam₀ < lam ≤ 1)
  by_cases hsmall : lam ≤ lam₀
  · -- Case 1: plain Erdős-Szekeres suffices!
    have hk_exp : (k : ℝ) ≤ Real.exp (b * hEntN lam) := by
      have h1 : (k : ℝ) ≤ (Nat.choose (an + bn) an : ℝ) := by exact_mod_cast hk_le_choose
      have h2 := choose_le_exp_binEntropy ha1_nat hb1_nat
      have h3 := binEntropy_eq_div_mul_hEntN ha0 hb0
      exact h1.trans (h2.trans (by rw [h3]))
    have hlogk_le : Real.log (k : ℝ) ≤ b * hEntN lam := by
      have hk_rpos : (0 : ℝ) < k := by exact_mod_cast hk1
      calc Real.log (k : ℝ) ≤ Real.log (Real.exp (b * hEntN lam)) := Real.log_le_log hk_rpos hk_exp
        _ = b * hEntN lam := Real.log_exp _
    have hh_le : hEntN lam ≤ 6 * lam ^ ((3 : ℝ) / 4) := hEntN_le_six_rpow hlam0 hlam1
    have hsq_h : (hEntN lam) ^ 2 ≤ 36 * Real.sqrt lam * lam := by
      have hhh_nn : 0 ≤ hEntN lam := by
        unfold hEntN
        have h1 : 0 ≤ (1 + lam) * Real.log (1 + lam) := mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
        have h2 : lam * Real.log lam ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0.le (Real.log_nonpos hlam0.le hlam1)
        linarith
      have h1 : (hEntN lam) ^ 2 ≤ (6 * lam ^ ((3 : ℝ) / 4)) ^ 2 := pow_le_pow_left₀ hhh_nn hh_le 2
      have h2 : (6 * lam ^ ((3 : ℝ) / 4)) ^ 2 = 36 * (Real.sqrt lam * lam) := by
        rw [mul_pow, ← Real.rpow_natCast (lam ^ _), ← Real.rpow_mul hlam0.le, Real.sqrt_eq_rpow]
        have heq : lam ^ ((1 : ℝ) / 2) * lam = lam ^ ((3 : ℝ) / 4 * (2 : ℕ)) := by
          rw [← Real.rpow_add_one hlam0.ne']; congr 1; norm_num
        rw [heq]; ring
      linarith only [h1, h2]
    have hsqrt_lam : Real.sqrt lam ≤ δ * (Real.log 2) ^ 2 / 36 := by
      have h1 := Real.sqrt_le_sqrt (hsmall.trans hlam₀_sq)
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hlogk_sq : (Real.log (k : ℝ)) ^ 2 ≤ δ * (Real.log 2) ^ 2 * (a * b) := by
      have h1 : (Real.log (k : ℝ)) ^ 2 ≤ (b * hEntN lam) ^ 2 := pow_le_pow_left₀ hlogk_nn hlogk_le 2
      have h2 : b ^ 2 * lam = a * b := by dsimp [lam]; field_simp [hb0.ne']
      calc (Real.log (k : ℝ)) ^ 2
          ≤ b ^ 2 * (hEntN lam) ^ 2 := by rw [mul_pow] at h1; exact h1
        _ ≤ b ^ 2 * (36 * Real.sqrt lam * lam) := mul_le_mul_of_nonneg_left hsq_h (sq_nonneg b)
        _ = (36 * Real.sqrt lam) * (b ^ 2 * lam) := by ring
        _ = (36 * Real.sqrt lam) * (a * b) := by rw [h2]
        _ ≤ (δ * (Real.log 2) ^ 2) * (a * b) := by
            have : 36 * Real.sqrt lam ≤ δ * (Real.log 2) ^ 2 := by linarith only [hsqrt_lam]
            exact mul_le_mul_of_nonneg_right this (by positivity)
    have hlogb_sq : (Real.logb 2 (k : ℝ)) ^ 2 ≤ δ * (a * b) := by
      rw [hlogb_eq, div_pow, div_le_iff₀ (sq_pos_of_pos hlog2)]
      linarith only [hlogk_sq]
    have hterm_nn : 0 ≤ ((Real.binEntropy x - (0.14 / Real.exp 1) * x) /
        (Real.log 2 * Real.sqrt (x * (1 - x)))) ^ 2 * (a * b) := by positivity
    linarith only [hlogb_sq, hterm_nn]
  · -- Case 2: lam₀ < lam ≤ 1 — use ramsey_F003!
    have hlam_gt : lam₀ < lam := lt_of_not_ge hsmall
    have hK_le : K_ram ≤ bn + 1 := by
      have : K_ram ≤ B0 := (le_max_left K_ram B1).trans (le_max_left _ 2)
      omega
    have hR_bound := hK_ram (bn + 1) (an + 1) hK_le (by omega) (by omega)
    have hk_le_exp : (k : ℝ) ≤ Real.exp ((FFn (3 / 100) (((an + 1 : ℕ) : ℝ) / ((bn + 1 : ℕ) : ℝ)) + ε) * ((bn + 1 : ℕ) : ℝ)) :=
      (by exact_mod_cast hk_lt_R.le : (k : ℝ) ≤ (ramsey (bn + 1) (an + 1) : ℝ)).trans hR_bound
    have hlogk_le1 : Real.log (k : ℝ) ≤ (FFn (3 / 100) ((a + 1) / (b + 1)) + ε) * (b + 1) := by
      have hk_rpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hcast : ((an + 1 : ℕ) : ℝ) = a + 1 := by push_cast; rfl
      have hcast2 : ((bn + 1 : ℕ) : ℝ) = b + 1 := by push_cast; rfl
      rw [hcast, hcast2] at hk_le_exp
      calc Real.log (k : ℝ) ≤ Real.log (Real.exp ((FFn (3 / 100) ((a + 1) / (b + 1)) + ε) * (b + 1))) :=
            Real.log_le_log hk_rpos hk_le_exp
        _ = (FFn (3 / 100) ((a + 1) / (b + 1)) + ε) * (b + 1) := Real.log_exp _
    -- Compare FFn (3/100) ((a+1)/(b+1)) * (b+1) with FFn (3/100) lam * b via concavity
    set lam1 : ℝ := (a + 1) / (b + 1)
    have hlam1_ge : lam ≤ lam1 := by
      dsimp [lam, lam1]
      rw [div_le_div_iff₀ hb0 (by linarith only [hb0])]
      nlinarith only [ha0, hb0, hab_le]
    have hlam1_le1 : lam1 ≤ 1 := (div_le_one (by linarith only [hb0])).2 (by linarith only [hab_le])
    have hlam1_diff : lam1 - lam ≤ 1 / b := by
      dsimp [lam, lam1]
      have heq : (a + 1) / (b + 1) - a / b = (b - a) / (b * (b + 1)) := by
        field_simp [hb0.ne', (show b + 1 ≠ 0 by linarith only [hb0])]; ring
      rw [heq, div_le_div_iff₀ (by positivity) hb0]
      nlinarith only [ha0, hb0, hab_le]
    have hF_shift : FFn (3 / 100) lam1 ≤ FFn (3 / 100) lam + FFn' (3 / 100) lam₀ * (1 / b) := by
      have htan := tangent_le_of_antitone_deriv (FFn (3 / 100)) (FFn' (3 / 100))
        (fun s hs => hasDerivAt_FFn (3 / 100) hs.1)
        (FFn'_anti (by norm_num) (by norm_num))
        ⟨hlam0, hlam1⟩ ⟨hlam0.trans_le hlam1_ge, hlam1_le1⟩
      have hFp_le : FFn' (3 / 100) lam ≤ FFn' (3 / 100) lam₀ :=
        FFn'_anti (by norm_num) (by norm_num) ⟨hlam₀_pos, hlam₀_le.trans (by norm_num)⟩ ⟨hlam0, hlam1⟩ hlam_gt.le
      have hFp_nn : 0 ≤ FFn' (3 / 100) lam₀ := (FFn'_pos (by norm_num) (by norm_num) hlam₀_pos (by linarith only [hlam₀_le])).le
      have hdiff_nn : 0 ≤ lam1 - lam := sub_nonneg.2 hlam1_ge
      have hm1 := mul_le_mul_of_nonneg_right hFp_le hdiff_nn
      have hm2 := mul_le_mul_of_nonneg_left hlam1_diff hFp_nn
      linarith only [htan, hm1, hm2]
    have hF_le1 : FFn (3 / 100) lam ≤ FFn (3 / 100) 1 :=
      FFn_mono (by norm_num) (by norm_num) ⟨hlam0, hlam1⟩ ⟨zero_lt_one, le_rfl⟩ hlam1
    have hC_le_εb : C_shift ≤ ε * b := by
      have hB1_le : B1 ≤ bn := ((le_max_right K_ram B1).trans (le_max_left _ 2)).trans hbn_ge
      have hlt : C_shift / ε < b := hB1.trans_le (Nat.cast_le.2 hB1_le)
      have := ((div_lt_iff₀ hε_pos).1 hlt).le
      linarith only [this]
    have hlogk_le2 : Real.log (k : ℝ) ≤ (FFn (3 / 100) lam + 2 * ε) * b := by
      have hmul : (FFn (3 / 100) lam1 + ε) * (b + 1) ≤
          (FFn (3 / 100) lam + ε) * b + FFn (3 / 100) lam + FFn' (3 / 100) lam₀ * (1 + 1 / b) + ε := by
        have h1 := mul_le_mul_of_nonneg_right (by linarith only [hF_shift] :
            FFn (3 / 100) lam1 + ε ≤ FFn (3 / 100) lam + FFn' (3 / 100) lam₀ * (1 / b) + ε)
            (show 0 ≤ b + 1 by linarith only [hb0])
        have heq : (FFn (3 / 100) lam + FFn' (3 / 100) lam₀ * (1 / b) + ε) * (b + 1) =
            (FFn (3 / 100) lam + ε) * b + FFn (3 / 100) lam + FFn' (3 / 100) lam₀ * (1 + 1 / b) + ε := by
          field_simp [hb0.ne']; ring
        rwa [heq] at h1
      have h1b_le : 1 + 1 / b ≤ 2 := by
        have : 1 / b ≤ 1 := (div_le_one hb0).2 (Nat.one_le_cast.2 hb1_nat)
        linarith only [this]
      have hFp_nn : 0 ≤ FFn' (3 / 100) lam₀ := (FFn'_pos (by norm_num) (by norm_num) hlam₀_pos (by linarith only [hlam₀_le])).le
      have hprod_le : FFn' (3 / 100) lam₀ * (1 + 1 / b) ≤ 2 * FFn' (3 / 100) lam₀ := by nlinarith only [h1b_le, hFp_nn]
      dsimp [C_shift] at hC_le_εb
      linarith only [hlogk_le1, hmul, hF_le1, hprod_le, hC_le_εb]
    -- Relate FFn (3/100) lam to binEntropy x - (0.14 / exp 1) * x
    have hF_le_target : FFn (3 / 100) lam ≤ hEntN lam - (0.14 / Real.exp 1) * lam := by
      unfold FFn
      have hg := gFn_003_le hlam0 hlam1
      have h14 : (14 / 100 : ℝ) = 0.14 := by norm_num
      rw [h14] at hg
      linarith
    have hF_le_2 : FFn (3 / 100) lam ≤ 2 := by
      have h1 : FFn (3 / 100) 1 ≤ 2 := by
        unfold FFn hEntN gFn
        rw [Real.log_one]
        have hlog2_ub : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
        have hg_neg : (-(1 / 4) * (1 : ℝ) + (3 / 100) * 1 ^ 2 + (2 / 25) * 1 ^ 3) * Real.exp (-1) ≤ 0 := by
          have : -(1 / 4 : ℝ) * 1 + (3 / 100) * 1 ^ 2 + (2 / 25) * 1 ^ 3 ≤ 0 := by norm_num
          exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
        have h2 : (1 + (1 : ℝ)) * Real.log (1 + 1) = 2 * Real.log 2 := by norm_num
        linarith
      exact hF_le1.trans h1
    have hF_nn : 0 ≤ FFn (3 / 100) lam := FFn_pos (by norm_num) (by norm_num) hlam0 hlam1
    -- Square hlogk_le2 and absorb error into δ * (Real.log 2)^2 * (a * b)
    have hsq_k : (Real.log (k : ℝ)) ^ 2 ≤
        (b * (hEntN lam - (0.14 / Real.exp 1) * lam)) ^ 2 + δ * (Real.log 2) ^ 2 * (a * b) := by
      have h1 : (Real.log (k : ℝ)) ^ 2 ≤ ((FFn (3 / 100) lam + 2 * ε) * b) ^ 2 :=
        pow_le_pow_left₀ hlogk_nn hlogk_le2 2
      have h2 : (FFn (3 / 100) lam + 2 * ε) ^ 2 ≤ (FFn (3 / 100) lam) ^ 2 + 12 * ε := by
        nlinarith only [hF_le_2, hF_nn, hε_le1, hε_pos]
      have h3 : (FFn (3 / 100) lam) ^ 2 ≤ (hEntN lam - (0.14 / Real.exp 1) * lam) ^ 2 :=
        pow_le_pow_left₀ hF_nn hF_le_target 2
      have h4 : 12 * ε * b ^ 2 ≤ δ * (Real.log 2) ^ 2 * (a * b) := by
        have hlam_ab : lam * b ^ 2 = a * b := by dsimp [lam]; field_simp [hb0.ne']
        calc 12 * ε * b ^ 2
            ≤ (δ * lam₀ * (Real.log 2) ^ 2) * b ^ 2 := mul_le_mul_of_nonneg_right hε_bd (sq_nonneg b)
          _ ≤ (δ * lam * (Real.log 2) ^ 2) * b ^ 2 := by
              have : δ * lam₀ * (Real.log 2) ^ 2 ≤ δ * lam * (Real.log 2) ^ 2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam_gt.le hδ.le) (sq_nonneg _)
              exact mul_le_mul_of_nonneg_right this (sq_nonneg b)
          _ = δ * (Real.log 2) ^ 2 * (lam * b ^ 2) := by ring
          _ = δ * (Real.log 2) ^ 2 * (a * b) := by rw [hlam_ab]
      calc (Real.log (k : ℝ)) ^ 2
          ≤ (FFn (3 / 100) lam + 2 * ε) ^ 2 * b ^ 2 := by rw [mul_pow] at h1; exact h1
        _ ≤ ((FFn (3 / 100) lam) ^ 2 + 12 * ε) * b ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg b)
        _ = (FFn (3 / 100) lam) ^ 2 * b ^ 2 + 12 * ε * b ^ 2 := by ring
        _ ≤ (hEntN lam - (0.14 / Real.exp 1) * lam) ^ 2 * b ^ 2 + δ * (Real.log 2) ^ 2 * (a * b) :=
            add_le_add (mul_le_mul_of_nonneg_right h3 (sq_nonneg b)) h4
        _ = (b * (hEntN lam - (0.14 / Real.exp 1) * lam)) ^ 2 + δ * (Real.log 2) ^ 2 * (a * b) := by ring
    -- Convert to target RHS via exact identity
    have hnum_eq : (a + b) * (Real.binEntropy x - (0.14 / Real.exp 1) * x) =
        b * (hEntN lam - (0.14 / Real.exp 1) * lam) := by
      have hent := binEntropy_eq_div_mul_hEntN ha0 hb0
      have hax : (a + b) * x = a := by dsimp [x]; field_simp [hab_pos.ne']
      have hbl : b * lam = a := by dsimp [lam]; field_simp [hb0.ne']
      calc (a + b) * (Real.binEntropy x - (0.14 / Real.exp 1) * x)
          = (a + b) * Real.binEntropy x - (0.14 / Real.exp 1) * ((a + b) * x) := by ring
        _ = b * hEntN lam - (0.14 / Real.exp 1) * (b * lam) := by rw [hent, hax, hbl]
        _ = b * (hEntN lam - (0.14 / Real.exp 1) * lam) := by ring
    have hrhs_eq : (((Real.binEntropy x - (0.14 / Real.exp 1) * x) /
        (Real.log 2 * Real.sqrt (x * (1 - x)))) ^ 2 + δ) * (a * b) =
        ((b * (hEntN lam - (0.14 / Real.exp 1) * lam)) ^ 2 + δ * (Real.log 2) ^ 2 * (a * b)) /
        (Real.log 2) ^ 2 := by
      rw [hsqrt]
      have hsq_ab : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
      have hsq_pos : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (by positivity)
      have hfrac : (Real.binEntropy x - (0.14 / Real.exp 1) * x) /
          (Real.log 2 * (Real.sqrt (a * b) / (a + b))) =
          (b * (hEntN lam - (0.14 / Real.exp 1) * lam)) / (Real.log 2 * Real.sqrt (a * b)) := by
        rw [← hnum_eq]
        field_simp [hlog2.ne', hsq_pos.ne', hab_pos.ne']
      rw [hfrac, div_pow, mul_pow, mul_pow, hsq_ab]
      field_simp [hlog2.ne', (show a * b ≠ 0 by positivity)]
    rw [hlogb_eq, div_pow, hrhs_eq]
    exact div_le_div_of_nonneg_right hsq_k (sq_nonneg _)

end Erdos627AFM

theorem OMA.solution : OMA.R_Erdos627_erdos_627_variants_afm_upper_R1.H1 := by
  intro δ hδ
  obtain ⟨K0, hK0⟩ := Erdos627AFM.h1_wlog_le δ hδ
  refine Filter.eventually_atTop.2 ⟨K0, fun k hk H => ?_⟩
  by_cases hle : H.cliqueNum ≤ H.indepNum
  · exact hK0 k hk H hle
  · have hle_c : Hᶜ.cliqueNum ≤ Hᶜ.indepNum := by
      rw [SimpleGraph.cliqueNum_compl, SimpleGraph.indepNum_compl]
      omega
    have hc := hK0 k hk Hᶜ hle_c
    simp only [SimpleGraph.cliqueNum_compl, SimpleGraph.indepNum_compl] at hc
    simpa only [min_comm, add_comm, mul_comm] using hc
