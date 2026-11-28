import FormalConjectures.ErdosProblems.«65»

-- Problem: Erdős Problem 65 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/65.lean:50 (declaration Erdos65.erdos_65.parts.i)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

noncomputable section

open Classical

namespace OMA65

open SimpleGraph Finset

/-- Restriction of `G` to the vertex set `S` (as a graph on the same type). -/
def restr {V : Type} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

lemma restr_adj {V : Type} (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (restr G S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl

lemma restr_le {V : Type} (G : SimpleGraph V) (S : Finset V) : restr G S ≤ G :=
  fun _ _ h => ((restr_adj G S _ _).1 h).1

lemma cycleLengths_mono {V : Type} {G H : SimpleGraph V} (h : H ≤ G) :
    H.cycleLengths ⊆ G.cycleLengths := by
  rintro m ⟨a, w, hw, rfl⟩
  exact ⟨a, w.mapLe h, hw.mapLe h, by simp⟩

lemma cycleLengths_le_card {V : Type} [Fintype V] (G : SimpleGraph V) {m : ℕ}
    (hm : m ∈ G.cycleLengths) : m ≤ Fintype.card V := by
  obtain ⟨a, w, hw, rfl⟩ := hm
  have h1 := hw.support_nodup
  have h2 : w.support.tail.length = w.length := by
    rw [List.length_tail, Walk.length_support]; simp
  rw [← h2]
  exact h1.length_le_card

lemma cycleLengths_pos {V : Type} (G : SimpleGraph V) {m : ℕ}
    (hm : m ∈ G.cycleLengths) : 3 ≤ m := by
  obtain ⟨a, w, hw, rfl⟩ := hm
  exact hw.three_le_length

/-- the finite set of cycle lengths -/
def CF {V : Type} [Fintype V] (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter (· ∈ G.cycleLengths)

lemma coe_CF {V : Type} [Fintype V] (G : SimpleGraph V) : (↑(CF G) : Set ℕ) = G.cycleLengths := by
  ext m
  simp only [CF, coe_filter, mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨Nat.lt_succ_of_le (cycleLengths_le_card G h), h⟩

/-- the harmonic weight of the cycle spectrum -/
def W {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ := ∑ a ∈ CF G, (1 : ℝ) / a

lemma finsum_eq_W {V : Type} [Fintype V] (G : SimpleGraph V) :
    (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) = W G := by
  rw [← coe_CF, finsum_mem_coe_finset]; rfl

lemma W_nonneg {V : Type} [Fintype V] (G : SimpleGraph V) : 0 ≤ W G :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma W_mono {V : Type} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) : W H ≤ W G := by
  unfold W
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [CF, mem_filter] at hm ⊢
    exact ⟨hm.1, cycleLengths_mono h hm.2⟩
  · intro _ _ _; positivity

/-- degree of `v` inside `S` -/
def dS {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

lemma sum_dS_erase {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) {v : V}
    (hv : v ∈ S) :
    ∑ u ∈ S, dS G S u = ∑ u ∈ S.erase v, dS G (S.erase v) u + 2 * dS G S v := by
  rw [← Finset.add_sum_erase S _ hv]
  have key : ∀ u ∈ S.erase v, dS G S u = dS G (S.erase v) u + if G.Adj u v then 1 else 0 := by
    intro u hu
    unfold dS
    have : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    conv_lhs => rw [this]
    rw [Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have h2 : ∑ u ∈ S.erase v, (if G.Adj u v then 1 else 0) = dS G S v := by
    rw [Finset.sum_boole]
    unfold dS
    simp only [Nat.cast_id]
    have : (S.erase v).filter (fun u => G.Adj u v) = S.filter (G.Adj v) := by
      ext u
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨fun e => G.loopless.irrefl _ (e ▸ h2), h1⟩, h2.symm⟩
    rw [this]
  rw [h2]; ring

/-- A nonempty vertex set in which every vertex has more than `k` neighbours. -/
lemma exists_dense_subset {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℝ) (hk : 0 < k)
    (S0 : Finset V) (hS0 : S0.Nonempty)
    (h0 : 2 * k * S0.card ≤ ∑ u ∈ S0, (dS G S0 u : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, k < dS G S v := by
  let P : Finset V → Prop := fun S => S.Nonempty ∧ 2 * k * S.card ≤ ∑ u ∈ S, (dS G S u : ℝ)
  have hne : ((Finset.univ : Finset (Finset V)).filter P).Nonempty := ⟨S0, by simp [P, hS0, h0]⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [mem_filter, mem_univ, true_and, P] at hS hmin
  refine ⟨S, hS.1, fun v hv => ?_⟩
  have hsum := sum_dS_erase G S hv
  have hcast : (∑ u ∈ S, (dS G S u : ℝ)) =
      ∑ u ∈ S.erase v, (dS G (S.erase v) u : ℝ) + 2 * (dS G S v : ℝ) := by
    exact_mod_cast hsum
  by_cases hsing : (S.erase v).Nonempty
  · have hlt : ¬ (2 * k * (S.erase v).card ≤ ∑ u ∈ S.erase v, (dS G (S.erase v) u : ℝ)) := by
      intro h
      have := hmin _ ⟨hsing, h⟩
      rw [Finset.card_erase_of_mem hv] at this
      have : 0 < S.card := Finset.card_pos.mpr hS.1
      omega
    push Not at hlt
    have hc : ((S.erase v).card : ℝ) = S.card - 1 := by
      rw [Finset.card_erase_of_mem hv]
      have : 1 ≤ S.card := Finset.card_pos.mpr hS.1
      push_cast [this]; ring
    have := hS.2
    rw [hcast] at this
    rw [hc] at hlt
    nlinarith
  · have he : S.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsing
    have hS1 : S = {v} := by
      have := Finset.insert_erase hv
      rw [he] at this; exact this.symm
    have := hS.2
    subst hS1
    have h0 : (({v} : Finset V).filter (G.Adj v)).card = 0 := by
      rw [Finset.filter_singleton, if_neg (G.loopless.irrefl v)]; rfl
    rw [Finset.sum_singleton, Finset.card_singleton] at this
    unfold dS at this
    rw [h0] at this
    simp at this
    linarith

/-- The min-degree form of the Gyárfás–Komlós–Szemerédi theorem. -/
def MGT : Prop :=
  ∃ β > (0 : ℝ), ∃ γ : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (S : Finset V) (d : ℕ),
    S.Nonempty → (∀ v ∈ S, d ≤ dS G S v) → β * Real.log d - γ ≤ W G


/-- weight of the cycle lengths above `A` -/
def wAbove {V : Type} [Fintype V] (G : SimpleGraph V) (A : ℕ) : ℝ :=
  ∑ a ∈ (CF G).filter (A < ·), (1 : ℝ) / a

lemma cycle_le_of_supported {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (hG : ∀ u v, G.Adj u v → v ∈ S) {m : ℕ} (hm : m ∈ G.cycleLengths) : m ≤ S.card := by
  obtain ⟨a, w, hw, rfl⟩ := hm
  have h1 := hw.support_nodup
  have h2 : w.support.tail.length = w.length := by
    rw [List.length_tail, Walk.length_support]; simp
  rw [← h2, ← List.toFinset_card_of_nodup h1]
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset, ← Walk.map_snd_darts, List.mem_map] at hx
  obtain ⟨d, _, rfl⟩ := hx
  exact hG _ _ d.adj

lemma restr_supported {V : Type} (G : SimpleGraph V) (S : Finset V) :
    ∀ u v, (restr G S).Adj u v → v ∈ S := fun _ _ h => h.2.2

/-- The Main Lemma (GKS Theorem 3 in potential form). -/
def ML : Prop :=
  ∃ d0 : ℕ, 1 ≤ d0 ∧ ∃ K : ℕ, 1 ≤ K ∧ 2 * K ≤ d0 ∧ ∃ w0 > (0 : ℝ), ∃ α > (0 : ℝ),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (S : Finset V) (d : ℕ),
      S.Nonempty → d0 ≤ d → (∀ v ∈ S, d ≤ dS G S v) → (∀ u v, G.Adj u v → v ∈ S) →
      α * Real.log d ≤ W G ∨
      ∃ H : SimpleGraph V, H ≤ G ∧ ∃ T : Finset V, T.Nonempty ∧ (∀ v ∈ T, d / K ≤ dS H T v) ∧
        w0 ≤ wAbove G T.card

lemma W_split {V : Type} [Fintype V] (G H : SimpleGraph V) (T : Finset V) (hHG : H ≤ G)
    (hH : ∀ u v, H.Adj u v → v ∈ T) : W H + wAbove G T.card ≤ W G := by
  unfold W wAbove
  rw [← Finset.sum_filter_add_sum_filter_not (CF G) (T.card < ·)]
  have h1 : ∑ a ∈ CF H, (1 : ℝ) / a ≤ ∑ a ∈ (CF G).filter (fun a => ¬ T.card < a), (1 : ℝ) / a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [CF, mem_filter] at hm ⊢
      exact ⟨⟨hm.1, cycleLengths_mono hHG hm.2⟩, not_lt.mpr (cycle_le_of_supported H T hH hm.2)⟩
    · intro _ _ _; positivity
  linarith

lemma dS_restr {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) :
    dS (restr G S) S v = dS G S v := by
  unfold dS; congr 1; ext x
  simp only [mem_filter, restr_adj]
  exact ⟨fun ⟨h1, h2, _, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hv, h1⟩⟩

lemma MGT_of_ML (hML : ML) : MGT := by
  obtain ⟨d0, hd0, K, hK, hKd0, w0, hw0, α, hα, hML⟩ := hML
  have hlK : 0 < Real.log (2 * K) := Real.log_pos (by norm_cast; omega)
  set β := min α (w0 / Real.log (2 * K)) with hβdef
  have hβ : 0 < β := lt_min hα (div_pos hw0 hlK)
  set γ := β * Real.log d0 with hγdef
  have hγ : 0 ≤ γ := mul_nonneg hβ.le (Real.log_nonneg (by exact_mod_cast hd0))
  refine ⟨β, hβ, γ, ?_⟩
  -- strong induction on the size of the support
  suffices key : ∀ N : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (S : Finset V) (d : ℕ),
      S.card ≤ N → S.Nonempty → (∀ v ∈ S, d ≤ dS G S v) → β * Real.log d - γ ≤ W (restr G S) by
    intro V _ G S d hS hd
    exact le_trans (key S.card V G S d le_rfl hS hd) (W_mono (restr_le G S))
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ G S d hSN hS hd
  by_cases hsmall : d < d0
  · have : β * Real.log d ≤ γ := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp; exact hγ
      · exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hsmall.le)) hβ.le
    linarith [W_nonneg (restr G S)]
  push Not at hsmall
  have hd' : ∀ v ∈ S, d ≤ dS (restr G S) S v := fun v hv => (dS_restr G S hv).symm ▸ hd v hv
  rcases hML V (restr G S) S d hS hsmall hd' (restr_supported G S) with h | ⟨H, hH, T, hT, hTd, hw⟩
  · have h1 : β * Real.log d ≤ α * Real.log d :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.log_nonneg (by exact_mod_cast (le_trans hd0 hsmall)))
    linarith
  · -- T is strictly smaller than S
    have hpos : 0 < wAbove (restr G S) T.card := lt_of_lt_of_le hw0 hw
    have hTS : T.card < S.card := by
      by_contra hcon
      push Not at hcon
      apply (lt_irrefl (0 : ℝ))
      calc (0 : ℝ) < wAbove (restr G S) T.card := hpos
        _ = 0 := by
          unfold wAbove
          apply Finset.sum_eq_zero
          intro m hm
          simp only [CF, mem_filter] at hm
          have := cycle_le_of_supported _ S (restr_supported G S) hm.1.2
          omega
    have ih' := ih T.card (lt_of_lt_of_le hTS hSN) V H T (d / K) le_rfl hT hTd
    have hsplit := W_split (restr G S) (restr H T) T (le_trans (restr_le H T) hH)
      (restr_supported H T)
    -- log (d / K) ≥ log d - log (2K)
    have hdK : (d : ℝ) / (2 * K) ≤ ((d / K : ℕ) : ℝ) := by
      have h1 : (d : ℝ) / K - 1 ≤ ((d / K : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := d) (b := K) (by omega)
        rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
        have : (d : ℝ) < ((d / K : ℕ) : ℝ) * K + K := by exact_mod_cast this
        linarith
      have h2 : (d : ℝ) / (2 * K) ≤ (d : ℝ) / K - 1 := by
        have hdK2 : (2 * K : ℝ) ≤ d := by exact_mod_cast (le_trans hKd0 hsmall)
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
        have : (d : ℝ) / K - 1 - d / (2 * K) = (d - 2 * K) / (2 * K) := by
          field_simp; ring
        have : 0 ≤ (d - 2 * K : ℝ) / (2 * K) := div_nonneg (by linarith) (by positivity)
        linarith
      linarith
    have hdpos : (0 : ℝ) < d / (2 * K) := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans hd0 hsmall)
      positivity
    have hlog : Real.log d - Real.log (2 * K) ≤ Real.log ((d / K : ℕ) : ℝ) := by
      have hdne : (d : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans hd0 hsmall)
        positivity
      have hKne : (2 * K : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK
        positivity
      rw [← Real.log_div hdne hKne]
      exact Real.log_le_log hdpos hdK
    have hβw : β * Real.log (2 * K) ≤ w0 := by
      have := mul_le_mul_of_nonneg_right (min_le_right α (w0 / Real.log (2 * K))) hlK.le
      rwa [div_mul_cancel₀ _ hlK.ne'] at this
    have := mul_le_mul_of_nonneg_left hlog hβ.le
    nlinarith

lemma main_of_MGT (hM : MGT) :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℝ in Filter.atTop,
      ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        0 < n →
        Fintype.card V = n →
        (G.edgeSet.ncard : ℝ) = k * n →
        (∑ᶠ a ∈ G.cycleLengths, (1 : ℝ) / a) ≥ c * Real.log k := by
  obtain ⟨β, hβ, γ, hM⟩ := hM
  refine ⟨β / 2, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max 1 (Real.exp (2 * γ / β)))] with k hk
  intro n V _ G hn hV hE
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hk0 : 0 < k := by linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]; omega
  have hsumdeg : ∑ u ∈ (Finset.univ : Finset V), (dS G Finset.univ u : ℝ) = 2 * k * n := by
    have h1 : ∀ u, dS G Finset.univ u = G.degree u := by
      intro u; unfold dS; rw [← G.card_neighborFinset_eq_degree]; congr 1; ext x; simp
    simp_rw [h1]
    have h2 := G.sum_degrees_eq_twice_card_edges
    have h3 : (G.edgeFinset.card : ℝ) = G.edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card' G.edgeSet]; simp [SimpleGraph.edgeFinset]
    rw [← Nat.cast_sum, h2]; push_cast; rw [h3, hE]; ring
  obtain ⟨S, hSne, hS⟩ := exists_dense_subset G k hk0 Finset.univ hne
    (by rw [hsumdeg, Finset.card_univ, hV])
  have hd : ∀ v ∈ S, ⌈k⌉₊ ≤ dS (restr G S) S v := by
    intro v hv
    have : dS (restr G S) S v = dS G S v := by
      unfold dS; congr 1; ext x
      simp only [mem_filter, restr_adj]
      exact ⟨fun ⟨h1, h2, _, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hv, h1⟩⟩
    rw [this]; exact Nat.ceil_le.mpr (hS v hv).le
  have hW := hM V (restr G S) S _ hSne hd
  rw [ge_iff_le, finsum_eq_W]
  refine le_trans ?_ (le_trans hW (W_mono (restr_le G S)))
  have hlog : Real.log k ≤ Real.log ⌈k⌉₊ := Real.log_le_log hk0 (Nat.le_ceil k)
  have hγ : 2 * γ / β ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hk0]; exact le_trans (le_max_right _ _) hk
  have : γ ≤ β / 2 * Real.log k := by
    have := mul_le_mul_of_nonneg_left hγ (le_of_lt (half_pos hβ))
    rw [show β / 2 * (2 * γ / β) = γ by field_simp] at this
    linarith
  nlinarith


lemma walk_of_fun {V : Type} (G : SimpleGraph V) (g : ℕ → V) (k : ℕ)
    (hadj : ∀ i, i < k → G.Adj (g i) (g (i + 1))) :
    ∃ p : G.Walk (g 0) (g k), p.support = (List.range (k + 1)).map g ∧ p.length = k := by
  induction k with
  | zero => exact ⟨Walk.nil, by simp, rfl⟩
  | succ k ih =>
    obtain ⟨p, hp, hl⟩ := ih (fun i hi => hadj i (by omega))
    refine ⟨p.concat (hadj k (by omega)), ?_, ?_⟩
    · rw [Walk.support_concat, hp, @List.range_succ (k + 1), List.map_append]
      rfl
    · simp [Walk.length_concat, hl]

/-- A cyclic sequence of `L ≥ 3` distinct vertices with consecutive adjacencies is a cycle. -/
lemma cycle_of_fun {V : Type} (G : SimpleGraph V) (L : ℕ) (hL : 3 ≤ L) (g : ℕ → V)
    (hadj : ∀ i, i + 1 < L → G.Adj (g i) (g (i + 1))) (hclose : G.Adj (g (L - 1)) (g 0))
    (hinj : ∀ i j, i < L → j < L → g i = g j → i = j) : L ∈ G.cycleLengths := by
  obtain ⟨p, hp, hl⟩ := walk_of_fun G g (L - 1) (fun i hi => hadj i (by omega))
  refine ⟨g (L - 1), Walk.cons hclose p, ?_, by simp [hl]; omega⟩
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by simp [hl]; omega⟩
  have hpath : p.IsPath := by
    rw [Walk.isPath_def, hp]
    apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    exact hinj x y (by omega) (by omega) hxy
  simpa [Walk.tail_cons] using hpath

/-- Gyárfás–Komlós–Szemerédi Lemma 3: a 2-colouring of `{0,…,s}` with both colours used realises
every difference `e ≤ s/3` that is not a multiple of some `m ≥ 2`. -/
lemma diff_lemma (s : ℕ) (P : ℕ → Prop) (h0 : P 0) (j : ℕ) (hj : j ≤ s) (hjP : ¬ P j) :
    ∃ m, 2 ≤ m ∧ ∀ e, 1 ≤ e → 3 * e ≤ s → ¬ m ∣ e →
      ∃ u v, u ≤ s ∧ v ≤ s ∧ P u ∧ ¬ P v ∧ (u + e = v ∨ v + e = u) := by
  let D : ℕ → Prop := fun e => ∃ u v, u ≤ s ∧ v ≤ s ∧ P u ∧ ¬ P v ∧ (u + e = v ∨ v + e = u)
  have hex : ∃ m, 1 ≤ m ∧ ¬ D m := ⟨s + 1, by omega, by
    rintro ⟨u, v, hu, hv, _, _, h | h⟩ <;> omega⟩
  let m := Nat.find hex
  have hm1 : 1 ≤ m := (Nat.find_spec hex).1
  have hmD : ¬ D m := (Nat.find_spec hex).2
  have hmin : ∀ e, 1 ≤ e → e < m → D e := by
    intro e he hem
    have := Nat.find_min hex hem
    push Not at this
    exact this he
  -- D 1 by a discrete intermediate value argument
  have hD1 : D 1 := by
    have hex2 : ∃ i, ¬ P i := ⟨j, hjP⟩
    let i0 := Nat.find hex2
    have hi0 : ¬ P i0 := Nat.find_spec hex2
    have hi0j : i0 ≤ j := Nat.find_min' hex2 hjP
    have hi0pos : i0 ≠ 0 := fun h => hi0 (h ▸ h0)
    have hprev : P (i0 - 1) := by
      have := Nat.find_min hex2 (show i0 - 1 < i0 by omega)
      push Not at this; exact this
    exact ⟨i0 - 1, i0, by omega, by omega, hprev, hi0, Or.inl (by omega)⟩
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m = 1 := by omega
    exact hmD (this ▸ hD1)
  -- periodicity
  have hper : ∀ x, x + m ≤ s → (P x ↔ P (x + m)) := by
    intro x hx
    constructor
    · intro hP; by_contra hQ; exact hmD ⟨x, x + m, by omega, hx, hP, hQ, Or.inl rfl⟩
    · intro hP; by_contra hQ; exact hmD ⟨x + m, x, hx, by omega, hP, hQ, Or.inr rfl⟩
  have hperq : ∀ q x, x + q * m ≤ s → (P x ↔ P (x + q * m)) := by
    intro q
    induction q with
    | zero => intro x _; simp
    | succ q ih =>
      intro x hx
      rw [ih x (by nlinarith), hper (x + q * m) (by nlinarith)]
      rw [show x + q * m + m = x + (q + 1) * m by ring]
  refine ⟨m, hm2, fun e he1 he3 hme => ?_⟩
  set t := e % m with ht
  set r := e / m with hr
  have hte : r * m + t = e := by rw [ht, hr, mul_comm]; exact Nat.div_add_mod e m
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hme
    · exact h
  have htm : t < m := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · have : e = t := by rw [← hte, hr0]; simp
    exact this ▸ hmin t ht1 htm
  obtain ⟨u0, v0, hu0, hv0, hPu, hPv, huv⟩ := hmin t ht1 htm
  have hrm : m ≤ r * m := by nlinarith
  rcases huv with huv | huv
  · -- u0 < v0 = u0 + t
    set q := u0 / m
    have hq : q * m ≤ u0 := Nat.div_mul_le_self u0 m
    have hu1 : u0 - q * m < m := by
      have := Nat.mod_lt u0 (show m > 0 by omega)
      rw [Nat.mod_eq_sub_mul_div] at this; rwa [mul_comm] at this
    have hPu1 : P (u0 - q * m) := by
      rw [hperq q (u0 - q * m) (by omega), Nat.sub_add_cancel hq]; exact hPu
    have hPv1 : ¬ P (v0 - q * m) := by
      rw [hperq q (v0 - q * m) (by omega), Nat.sub_add_cancel (by omega)]; exact hPv
    refine ⟨u0 - q * m, v0 - q * m + r * m, by omega, by omega, hPu1, ?_, Or.inl (by omega)⟩
    rw [← hperq r _ (by omega)]; exact hPv1
  · -- v0 < u0 = v0 + t
    set q := v0 / m
    have hq : q * m ≤ v0 := Nat.div_mul_le_self v0 m
    have hv1 : v0 - q * m < m := by
      have := Nat.mod_lt v0 (show m > 0 by omega)
      rw [Nat.mod_eq_sub_mul_div] at this; rwa [mul_comm] at this
    have hPv1 : ¬ P (v0 - q * m) := by
      rw [hperq q (v0 - q * m) (by omega), Nat.sub_add_cancel hq]; exact hPv
    have hPu1 : P (u0 - q * m) := by
      rw [hperq q (u0 - q * m) (by omega), Nat.sub_add_cancel (by omega)]; exact hPu
    refine ⟨u0 - q * m + r * m, v0 - q * m, by omega, by omega, ?_, hPv1, Or.inr (by omega)⟩
    rw [← hperq r _ (by omega)]; exact hPu1


section Tree

variable {V : Type} (G : SimpleGraph V) (par : V → V) (lev : V → ℕ)

/-- `par` is a parent function compatible with the levels `lev`. -/
def IsParent : Prop := ∀ v, 1 ≤ lev v → G.Adj v (par v) ∧ lev (par v) = lev v - 1

variable {G par lev}

lemma lev_iter (hP : IsParent G par lev) :
    ∀ t v, t ≤ lev v → lev (par^[t] v) = lev v - t := by
  intro t
  induction t with
  | zero => intro v _; simp
  | succ t ih =>
    intro v hv
    rw [Function.iterate_succ_apply']
    have h1 := ih v (by omega)
    rw [(hP _ (by omega)).2, h1]; omega

lemma adj_iter (hP : IsParent G par lev) (t : ℕ) (v : V) (ht : t + 1 ≤ lev v) :
    G.Adj (par^[t] v) (par^[t + 1] v) := by
  rw [Function.iterate_succ_apply']
  exact (hP _ (by rw [lev_iter hP t v (by omega)]; omega)).1

lemma iter_ne_of_ne (x y : V) {i j : ℕ} (hij : i ≤ j)
    (h : par^[j] x ≠ par^[j] y) : par^[i] x ≠ par^[i] y := by
  intro e; apply h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_add_apply, e]

/-- The basic cycle: a path segment `f a, …, f b` (all at level `≥ h`, ends at level `h`) closed by
the two tree paths to the common ancestor `c` levels below. -/
lemma pair_cycle (hP : IsParent G par lev) (f : ℕ → V) (a b h c : ℕ) (hab : a < b)
    (hc1 : 1 ≤ c) (hch : c ≤ h)
    (hadj : ∀ i, a ≤ i → i < b → G.Adj (f i) (f (i + 1)))
    (hinj : ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → f i = f j → i = j)
    (hlev : ∀ i, a ≤ i → i ≤ b → h ≤ lev (f i)) (hla : lev (f a) = h) (hlb : lev (f b) = h)
    (heq : par^[c] (f a) = par^[c] (f b)) (hne : par^[c - 1] (f a) ≠ par^[c - 1] (f b)) :
    (b - a) + 2 * c ∈ G.cycleLengths := by
  set n := b - a with hn
  set L := n + 2 * c with hL
  let g : ℕ → V := fun i =>
    if i ≤ n then f (a + i) else if i ≤ n + c then par^[i - n] (f b) else par^[L - i] (f a)
  have g1 : ∀ i, i ≤ n → g i = f (a + i) := fun i hi => by simp [g, hi]
  have g2 : ∀ i, n < i → i ≤ n + c → g i = par^[i - n] (f b) := fun i hi hi' => by
    simp [g, hi', show ¬ i ≤ n by omega]
  have g3 : ∀ i, n + c < i → g i = par^[L - i] (f a) := fun i hi => by
    simp [g, show ¬ i ≤ n by omega, show ¬ i ≤ n + c by omega]
  -- levels
  have lv2 : ∀ i, n < i → i ≤ n + c → lev (g i) = h - (i - n) := fun i hi hi' => by
    rw [g2 i hi hi', lev_iter hP _ _ (by omega), hlb]
  have lv3 : ∀ i, n + c < i → i < L → lev (g i) = h - (L - i) := fun i hi hi' => by
    rw [g3 i hi, lev_iter hP _ _ (by omega), hla]
  apply cycle_of_fun G L (by omega) g
  · intro i hi
    rcases Nat.lt_or_ge i n with h1 | h1
    · rw [g1 i h1.le, g1 (i + 1) h1]
      have := hadj (a + i) (by omega) (by omega)
      rwa [show a + i + 1 = a + (i + 1) by omega] at this
    rcases Nat.lt_or_ge i (n + c) with h2 | h2
    · by_cases h3 : i = n
      · subst h3
        rw [g1 _ le_rfl, g2 (n + 1) (by omega) (by omega)]
        rw [show a + n = b by omega, show n + 1 - n = 0 + 1 by omega]
        have := adj_iter hP 0 (f b) (by omega)
        simpa using this
      · rw [g2 i (by omega) (by omega), g2 (i + 1) (by omega) (by omega),
          show i + 1 - n = (i - n) + 1 by omega]
        exact adj_iter hP _ _ (by omega)
    · by_cases h3 : i = n + c
      · subst h3
        rw [g2 _ (by omega) le_rfl, g3 (n + c + 1) (by omega), show n + c - n = c by omega, heq.symm]
        rw [show L - (n + c + 1) = c - 1 by omega]
        have := adj_iter hP (c - 1) (f a) (by omega)
        rw [show c - 1 + 1 = c by omega] at this
        exact this.symm
      · rw [g3 i (by omega), g3 (i + 1) (by omega)]
        have := adj_iter hP (L - (i + 1)) (f a) (by omega)
        rw [show L - (i + 1) + 1 = L - i by omega] at this
        exact this.symm
  · -- closing edge
    by_cases hc : c = 1
    · subst hc
      rw [g2 (L - 1) (by omega) (by omega), g1 0 (by omega), show L - 1 - n = 1 by omega, add_zero]
      rw [← heq]
      have := adj_iter hP 0 (f a) (by omega)
      simpa using this.symm
    · rw [g3 (L - 1) (by omega), g1 0 (by omega), show L - (L - 1) = 0 + 1 by omega, add_zero]
      have := adj_iter hP 0 (f a) (by omega)
      simpa using this.symm
  · -- injectivity
    have key : ∀ i j, i < L → j < L → i < j → g i ≠ g j := by
      intro i j hi hj hij e
      rcases Nat.lt_or_ge n i with h1 | h1
      · -- both in tree parts
        rcases Nat.lt_or_ge (n + c) i with h2 | h2
        · -- both in part 3
          have := congrArg lev e
          rw [lv3 i h2 hi, lv3 j (by omega) hj] at this; omega
        · rcases Nat.lt_or_ge (n + c) j with h3 | h3
          · -- i in part 2, j in part 3
            have hl := congrArg lev e
            rw [lv2 i h1 h2, lv3 j h3 hj] at hl
            have hij' : i - n = L - j := by omega
            rw [g2 i h1 h2, g3 j h3, ← hij'] at e
            -- e : par^[i-n] (f b) = par^[i-n] (f a), with i - n ≤ c - 1
            exact iter_ne_of_ne (f a) (f b) (show i - n ≤ c - 1 by omega) hne e.symm
          · have := congrArg lev e
            rw [lv2 i h1 h2, lv2 j (by omega) h3] at this; omega
      · rcases Nat.lt_or_ge n j with h3 | h3
        · -- i in part 1, j in tree part: level comparison
          have hl := congrArg lev e
          rw [g1 i h1] at hl
          have := hlev (a + i) (by omega) (by omega)
          rcases Nat.lt_or_ge (n + c) j with h4 | h4
          · rw [lv3 j h4 hj] at hl; omega
          · rw [lv2 j h3 h4] at hl; omega
        · rw [g1 i h1, g1 j h3] at e
          have := hinj _ _ (by omega) (by omega) (by omega) (by omega) e
          omega
    intro i j hi hj e
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (key i j hi hj h)
    · exact h
    · exact absurd e.symm (key j i hj hi h)


/-- The engine: a path alternating at level `h` whose top vertices lie in one cone of height `≤ h`
gives cycles of almost all even lengths `2c + 2e`, `e ≤ s/3`. -/
lemma engine (hP : IsParent G par lev) (f : ℕ → V) (s h : ℕ) (hs : 1 ≤ s)
    (hadj : ∀ i, i < 2 * s → G.Adj (f i) (f (i + 1)))
    (hinj : ∀ i j, i ≤ 2 * s → j ≤ 2 * s → f i = f j → i = j)
    (hlev : ∀ i, i ≤ 2 * s → h ≤ lev (f i)) (htop : ∀ i, i ≤ s → lev (f (2 * i)) = h)
    (C : ℕ) (hC : C ≤ h) (hroot : ∀ i, i ≤ s → par^[C] (f (2 * i)) = par^[C] (f 0)) :
    ∃ c m, 1 ≤ c ∧ c ≤ h ∧ 2 ≤ m ∧
      ∀ e, 1 ≤ e → 3 * e ≤ s → ¬ m ∣ e → 2 * c + 2 * e ∈ G.cycleLengths := by
  have hex : ∃ c, ∀ i, i ≤ s → par^[c] (f (2 * i)) = par^[c] (f 0) := ⟨C, hroot⟩
  set c := Nat.find hex with hcdef
  have hc : ∀ i, i ≤ s → par^[c] (f (2 * i)) = par^[c] (f 0) := Nat.find_spec hex
  have hcC : c ≤ C := Nat.find_min' hex hroot
  have hc1 : 1 ≤ c := by
    by_contra h0
    have h0' : c = 0 := by omega
    have := hc 1 hs
    rw [h0'] at this
    have := hinj 2 0 (by omega) (by omega) (by simpa using this)
    omega
  have hmin : ¬ ∀ i, i ≤ s → par^[c - 1] (f (2 * i)) = par^[c - 1] (f 0) :=
    Nat.find_min hex (show c - 1 < c by omega)
  push Not at hmin
  obtain ⟨j, hj, hjne⟩ := hmin
  obtain ⟨m, hm2, hm⟩ := diff_lemma s (fun i => par^[c - 1] (f (2 * i)) = par^[c - 1] (f 0))
    (by simp) j hj hjne
  refine ⟨c, m, hc1, le_trans hcC hC, hm2, fun e he1 he3 hme => ?_⟩
  obtain ⟨u, v, hu, hv, hPu, hPv, huv⟩ := hm e he1 he3 hme
  have hne : par^[c - 1] (f (2 * u)) ≠ par^[c - 1] (f (2 * v)) := by
    intro h; apply hPv; rw [← h]; exact hPu
  have heq : par^[c] (f (2 * u)) = par^[c] (f (2 * v)) := by rw [hc u hu, hc v hv]
  have key : ∀ a b, a < b → b ≤ s → par^[c] (f (2 * a)) = par^[c] (f (2 * b)) →
      par^[c - 1] (f (2 * a)) ≠ par^[c - 1] (f (2 * b)) →
      (2 * b - 2 * a) + 2 * c ∈ G.cycleLengths := by
    intro a b hab hb he hn
    exact pair_cycle hP f (2 * a) (2 * b) h c (by omega) hc1 (le_trans hcC hC)
      (fun i _ hi => hadj i (by omega))
      (fun i j hi hi' hj hj' e => hinj i j (by omega) (by omega) e)
      (fun i _ hi => hlev i (by omega)) (htop a (by omega)) (htop b hb) he hn
  rcases huv with huv | huv
  · have := key u v (by omega) hv heq hne
    rwa [show 2 * v - 2 * u + 2 * c = 2 * c + 2 * e by omega] at this
  · have := key v u (by omega) hu heq.symm (Ne.symm hne)
    rwa [show 2 * u - 2 * v + 2 * c = 2 * c + 2 * e by omega] at this

end Tree

lemma log_le_harm (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log ((b : ℝ) / a) ≤ ∑ k ∈ Finset.Ico a b, (1 : ℝ) / k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have : Real.log (((b + 1 : ℕ) : ℝ) / a) = Real.log ((b : ℝ) / a) + Real.log (((b : ℝ) + 1) / b) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; push_cast; field_simp
    rw [this]
    have h2 : Real.log (((b : ℝ) + 1) / b) ≤ 1 / b := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((b : ℝ) + 1) / b by positivity)
      have e : ((b : ℝ) + 1) / b - 1 = 1 / b := by field_simp; ring
      linarith
    linarith

/-- Harmonic weight of an almost-all-even block of lengths `2c + 2e`, `E1 ≤ e ≤ E2`, `m ∤ e`. -/
lemma block_weight (Λ : Finset ℕ) (c m E1 E2 : ℕ) (hm : 2 ≤ m) (hE1 : 1 ≤ E1) (hE : E1 ≤ E2)
    (hΛ : ∀ e, E1 ≤ e → e ≤ E2 → ¬ m ∣ e → 2 * c + 2 * e ∈ Λ) :
    (1 / 4 : ℝ) * Real.log (((c + E2 + 1 : ℕ) : ℝ) / (c + E1 + 1 : ℕ)) ≤
      ∑ a ∈ Λ.filter (2 * c + 2 * E1 ≤ ·), (1 : ℝ) / a := by
  let f : ℕ → ℝ := fun e => if m ∣ e then 0 else 1 / (2 * c + 2 * e : ℕ)
  -- step 1: the block sum is below the Λ-sum
  have h1 : ∑ e ∈ Finset.Icc E1 E2, f e ≤ ∑ a ∈ Λ.filter (2 * c + 2 * E1 ≤ ·), (1 : ℝ) / a := by
    have : ∑ e ∈ Finset.Icc E1 E2, f e =
        ∑ e ∈ (Finset.Icc E1 E2).filter (fun e => ¬ m ∣ e), (1 : ℝ) / (2 * c + 2 * e : ℕ) := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro e _; simp only [f]; split_ifs <;> simp
    rw [this]
    rw [← Finset.sum_image (f := fun a : ℕ => (1 : ℝ) / a) (g := fun e => 2 * c + 2 * e)
      (by intro x _ y _ h; simp only at h; omega)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      obtain ⟨e, ⟨⟨he1, he2⟩, hme⟩, rfl⟩ := ha
      exact ⟨hΛ e he1 he2 hme, by omega⟩
    · intro _ _ _; positivity
  -- step 2: pairing e, e+1
  have h2 : ∑ e ∈ Finset.Ico E1 E2, (1 : ℝ) / (2 * c + 2 * e + 2 : ℕ) ≤
      2 * ∑ e ∈ Finset.Icc E1 E2, f e := by
    have hpt : ∀ e ∈ Finset.Ico E1 E2, (1 : ℝ) / (2 * c + 2 * e + 2 : ℕ) ≤ f e + f (e + 1) := by
      intro e _
      have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [f]; split_ifs <;> positivity
      by_cases h : m ∣ e
      · have h' : ¬ m ∣ (e + 1) := by
          intro h'; have := (Nat.dvd_add_right h).mp h'
          have := Nat.le_of_dvd one_pos this; omega
        have : f (e + 1) = 1 / (2 * c + 2 * (e + 1) : ℕ) := by simp [f, h']
        rw [this, show 2 * c + 2 * (e + 1) = 2 * c + 2 * e + 2 by ring]; linarith [hf0 e]
      · have : f e = 1 / (2 * c + 2 * e : ℕ) := by simp [f, h]
        rw [this]
        have : (1 : ℝ) / (2 * c + 2 * e + 2 : ℕ) ≤ 1 / (2 * c + 2 * e : ℕ) := by
          apply one_div_le_one_div_of_le
          · have : 1 ≤ e := by
              rcases Nat.eq_zero_or_pos e with h0 | h0
              · exact absurd (h0 ▸ dvd_zero m) h
              · exact h0
            positivity
          · push_cast; linarith
        linarith [hf0 (e + 1)]
    calc ∑ e ∈ Finset.Ico E1 E2, (1 : ℝ) / (2 * c + 2 * e + 2 : ℕ)
        ≤ ∑ e ∈ Finset.Ico E1 E2, (f e + f (e + 1)) := Finset.sum_le_sum hpt
      _ = ∑ e ∈ Finset.Ico E1 E2, f e + ∑ e ∈ Finset.Ico E1 E2, f (e + 1) := Finset.sum_add_distrib
      _ ≤ ∑ e ∈ Finset.Icc E1 E2, f e + ∑ e ∈ Finset.Icc E1 E2, f e := by
          have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [f]; split_ifs <;> positivity
          gcongr
          · intro x hx; simp only [Finset.mem_Ico, Finset.mem_Icc] at hx ⊢; omega
          · rw [← Finset.sum_image (g := fun e => e + 1) (f := f)
              (by intro x _ y _ h; simp only at h; omega)]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
              obtain ⟨y, hy, rfl⟩ := hx; omega
            · intro x _ _; exact hf0 x
      _ = 2 * ∑ e ∈ Finset.Icc E1 E2, f e := by ring
  -- step 3: harmonic lower bound
  have h3 : Real.log (((c + E2 + 1 : ℕ) : ℝ) / (c + E1 + 1 : ℕ)) ≤
      2 * ∑ e ∈ Finset.Ico E1 E2, (1 : ℝ) / (2 * c + 2 * e + 2 : ℕ) := by
    have := log_le_harm (c + E1 + 1) (c + E2 + 1) (by omega) (by omega)
    refine le_trans this (le_of_eq ?_)
    rw [Finset.mul_sum]
    rw [show Finset.Ico (c + E1 + 1) (c + E2 + 1) = (Finset.Ico E1 E2).map
      (addLeftEmbedding (c + 1)) by
        ext x; simp only [Finset.mem_Ico, Finset.mem_map, addLeftEmbedding_apply]
        constructor
        · intro hx; exact ⟨x - (c + 1), by omega, by omega⟩
        · rintro ⟨y, hy, rfl⟩; omega]
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro e _
    simp only [addLeftEmbedding_apply]
    push_cast
    field_simp
    ring
  linarith



section BFS

variable {V : Type} (B : SimpleGraph V) (r : V)

lemma exists_parent (v : V) (hv : 1 ≤ B.dist r v) :
    ∃ w, B.Adj v w ∧ B.dist r w = B.dist r v - 1 := by
  have hreach : B.Reachable r v := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hlen : p.reverse.length = B.dist r v := by rw [Walk.length_reverse, hp]
  generalize p.reverse = q at hlen
  cases q with
  | nil => simp at hv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    simp only [Walk.length_cons] at hlen
    have h1 : B.dist r w ≤ q.length := by
      have := dist_le q.reverse; rwa [Walk.length_reverse] at this
    have h2 : B.dist r v ≤ B.dist r w + 1 := by
      have hr : B.Reachable r w := ⟨q.reverse⟩
      obtain ⟨p', hp'⟩ := hr.exists_walk_length_eq_dist
      have := dist_le (p'.concat h.symm)
      rw [Walk.length_concat] at this; omega
    omega

lemma walk_parity (col : V → Bool) (hcol : ∀ u v, B.Adj u v → col u ≠ col v) :
    ∀ {u v : V} (p : B.Walk u v), (col v = col u ↔ Even p.length) := by
  intro u v p
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have := hcol _ _ h
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    cases hb : col b <;> cases ha : col a <;> cases hc : col c <;> simp_all

lemma dist_ne_of_adj (col : V → Bool) (hcol : ∀ u v, B.Adj u v → col u ≠ col v) {u v : V}
    (hu : B.Reachable r u) (huv : B.Adj u v) : B.dist r u ≠ B.dist r v := by
  intro e
  have hv : B.Reachable r v := hu.trans huv.reachable
  obtain ⟨p, hp⟩ := hu.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hv.exists_walk_length_eq_dist
  have h1 := walk_parity B col hcol p
  have h2 := walk_parity B col hcol q
  rw [hp] at h1; rw [hq, ← e] at h2
  have h3 := h1.trans h2.symm
  have := hcol _ _ huv
  cases hu' : col u <;> cases hv' : col v <;> cases hr' : col r <;> simp_all

lemma dist_adj_eq (col : V → Bool) (hcol : ∀ u v, B.Adj u v → col u ≠ col v) {u v : V}
    (hu : B.Reachable r u) (huv : B.Adj u v) :
    B.dist r v = B.dist r u + 1 ∨ B.dist r u = B.dist r v + 1 := by
  have h1 := dist_ne_of_adj B r col hcol hu huv
  rcases huv.diff_dist_adj (u := r) with h | h | h
  · exact absurd h.symm h1
  · left; exact h
  · right
    have : B.dist r u ≠ 0 := by
      intro h0; apply h1; rw [h, h0]
    omega

/-- BFS parent -/
def bpar (v : V) : V := if h : 1 ≤ B.dist r v then Classical.choose (exists_parent B r v h) else v

lemma bpar_isParent : IsParent B (bpar B r) (B.dist r ·) := by
  intro v hv
  simp only [bpar, dif_pos hv]
  exact Classical.choose_spec (exists_parent B r v hv)

lemma bpar_iter_root (x : V) (hx : 1 ≤ B.dist r x) : (bpar B r)^[B.dist r x] x = r := by
  have hP := bpar_isParent B r
  have hreach : ∀ t, t ≤ B.dist r x → B.Reachable r ((bpar B r)^[t] x) := by
    intro t
    induction t with
    | zero => intro _; exact Reachable.of_dist_ne_zero (by rw [Function.iterate_zero_apply]; omega)
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply']
      have := adj_iter hP t x ht
      rw [Function.iterate_succ_apply'] at this
      exact (ih (by omega)).trans this.reachable
  have h0 := lev_iter hP (B.dist r x) x le_rfl
  simp only [Nat.sub_self] at h0
  rcases (dist_eq_zero_iff_eq_or_not_reachable).mp h0 with h | h
  · exact h.symm
  · exact absurd (hreach _ le_rfl) h

end BFS


section Layers

variable {V : Type} [Fintype V] (B : SimpleGraph V) (r : V) (S : Finset V)

/-- BFS layer `i` (inside `S`). -/
def Lay (i : ℕ) : Finset V := S.filter (fun v => B.Reachable r v ∧ B.dist r v = i)

/-- edges between layer `i` and layer `i+1`, counted from below -/
def eUp (i : ℕ) : ℕ := ∑ v ∈ Lay B r S i, ((Lay B r S (i + 1)).filter (B.Adj v)).card

lemma eUp_comm (i : ℕ) :
    eUp B r S i = ∑ w ∈ Lay B r S (i + 1), ((Lay B r S i).filter (B.Adj w)).card := by
  unfold eUp
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro v _
  simp only [B.adj_comm]

variable (col : V → Bool) (hcol : ∀ u v, B.Adj u v → col u ≠ col v)
  (hsupp : ∀ u v, B.Adj u v → v ∈ S)
include hcol hsupp

lemma nbr_layer {i : ℕ} {v w : V} (hv : v ∈ Lay B r S i) (hvw : B.Adj v w) :
    w ∈ Lay B r S (i + 1) ∨ (1 ≤ i ∧ w ∈ Lay B r S (i - 1)) := by
  simp only [Lay, Finset.mem_filter] at hv ⊢
  obtain ⟨_, hr, hd⟩ := hv
  have hw : B.Reachable r w := hr.trans hvw.reachable
  rcases dist_adj_eq B r col hcol hr hvw with h | h
  · left; exact ⟨hsupp _ _ hvw, hw, by omega⟩
  · right; exact ⟨by omega, hsupp _ _ hvw, hw, by omega⟩

lemma deg_split {i : ℕ} (hi : 1 ≤ i) {v : V} (hv : v ∈ Lay B r S i) :
    dS B S v = ((Lay B r S (i + 1)).filter (B.Adj v)).card +
      ((Lay B r S (i - 1)).filter (B.Adj v)).card := by
  unfold dS
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨_, h⟩
      rcases nbr_layer B r S col hcol hsupp hv h with h' | h'
      · left; exact ⟨h', h⟩
      · right; exact ⟨h'.2, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨(Finset.mem_filter.mp h1).1, h2⟩
      · exact ⟨(Finset.mem_filter.mp h1).1, h2⟩
  · rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Lay, Finset.mem_filter] at h1 h2
    omega

lemma deg_root (hr : r ∈ S) : dS B S r = ((Lay B r S 1).filter (B.Adj r)).card := by
  unfold dS
  congr 1; ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    have hL : r ∈ Lay B r S 0 := by simp [Lay, hr]
    rcases nbr_layer B r S col hcol hsupp hL h with h' | h'
    · exact ⟨h', h⟩
    · omega
  · rintro ⟨h1, h2⟩; exact ⟨(Finset.mem_filter.mp h1).1, h2⟩

omit hcol hsupp in
lemma lay_zero (hr : r ∈ S) : Lay B r S 0 = {r} := by
  ext v
  simp only [Lay, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h1, h2⟩
    rcases (dist_eq_zero_iff_eq_or_not_reachable).mp h2 with h | h
    · exact h.symm
    · exact absurd h1 h
  · rintro rfl; exact ⟨hr, Reachable.refl _, by simp⟩

/-- Growth of sparse layers. -/
lemma layer_growth (hr : r ∈ S) (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : ∀ v ∈ S, μ ≤ dS B S v) (h : ℕ)
    (hsparse : ∀ j, j < h → (8 * eUp B r S j : ℝ) < μ * ((Lay B r S j).card + (Lay B r S (j + 1)).card)) :
    ∀ i, 1 ≤ i → i ≤ h → 5 ^ (i - 1) ≤ (Lay B r S i).card ∧
      (Lay B r S (i - 1)).card ≤ (Lay B r S i).card := by
  intro i hi1 hih
  induction i, hi1 using Nat.le_induction with
  | base =>
    have h1 : μ ≤ (Lay B r S 1).card := by
      have := hdeg r hr
      rw [deg_root B r S col hcol hsupp hr] at this
      exact le_trans this (Finset.card_filter_le _ _)
    rw [lay_zero B r S hr]
    simp only [pow_zero, Nat.sub_self, Finset.card_singleton]
    omega
  | succ i hi ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    -- degree sum over layer i
    have hsum : μ * (Lay B r S i).card ≤ eUp B r S i + eUp B r S (i - 1) := by
      have e1 := eUp_comm B r S (i - 1)
      rw [show i - 1 + 1 = i by omega] at e1
      rw [e1, eUp, mul_comm, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro v hv
      rw [← deg_split B r S col hcol hsupp hi hv]
      exact hdeg v (Finset.mem_filter.mp hv).1
    have hs1 := hsparse i (by omega)
    have hs2 := hsparse (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hs2
    have hsumR : (μ : ℝ) * (Lay B r S i).card ≤ eUp B r S i + eUp B r S (i - 1) := by
      exact_mod_cast hsum
    have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
    have key : (8 : ℝ) * (Lay B r S i).card <
        (Lay B r S (i - 1)).card + 2 * (Lay B r S i).card + (Lay B r S (i + 1)).card := by
      have : (μ : ℝ) * (8 * (Lay B r S i).card) <
          μ * ((Lay B r S (i - 1)).card + 2 * (Lay B r S i).card + (Lay B r S (i + 1)).card) := by
        nlinarith
      exact lt_of_mul_lt_mul_left this hμ'.le
    have ih2' : ((Lay B r S (i - 1)).card : ℝ) ≤ (Lay B r S i).card := by exact_mod_cast ih2
    have h5 : 5 * (Lay B r S i).card ≤ (Lay B r S (i + 1)).card := by
      have : (5 : ℝ) * (Lay B r S i).card < (Lay B r S (i + 1)).card := by linarith
      exact_mod_cast this.le
    refine ⟨?_, ?_⟩
    · rw [show i + 1 - 1 = (i - 1) + 1 by omega, pow_succ]; nlinarith
    · rw [show i + 1 - 1 = i by omega]; omega

end Layers


section Thm2

variable {V : Type} [Fintype V]

/-- longest path length -/
def LP (F : SimpleGraph V) : ℕ :=
  Nat.findGreatest (fun n => ∃ u v, ∃ p : F.Walk u v, p.IsPath ∧ p.length = n) (Fintype.card V)

lemma path_length_le_card (F : SimpleGraph V) {u v : V} (p : F.Walk u v) (hp : p.IsPath) :
    p.length ≤ Fintype.card V := by
  have := hp.support_nodup.length_le_card
  rw [Walk.length_support] at this; omega

lemma le_LP (F : SimpleGraph V) {u v : V} (p : F.Walk u v) (hp : p.IsPath) : p.length ≤ LP F :=
  Nat.le_findGreatest (path_length_le_card F p hp) ⟨u, v, p, hp, rfl⟩

lemma exists_LP (F : SimpleGraph V) (x : V) :
    ∃ u v, ∃ p : F.Walk u v, p.IsPath ∧ p.length = LP F := by
  have := Nat.findGreatest_spec (P := fun n => ∃ u v, ∃ p : F.Walk u v, p.IsPath ∧ p.length = n)
    (Nat.zero_le (Fintype.card V)) ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩
  exact this

variable (B : SimpleGraph V) (r : V) (S : Finset V)

/-- the layer-pair graph -/
def pairG (h : ℕ) : SimpleGraph V where
  Adj u v := B.Adj u v ∧ ((u ∈ Lay B r S h ∧ v ∈ Lay B r S (h + 1)) ∨
    (u ∈ Lay B r S (h + 1) ∧ v ∈ Lay B r S h))
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun _ h => B.loopless.irrefl _ h.1⟩

lemma pairG_adj (h : ℕ) (u v : V) : (pairG B r S h).Adj u v ↔ B.Adj u v ∧
    ((u ∈ Lay B r S h ∧ v ∈ Lay B r S (h + 1)) ∨ (u ∈ Lay B r S (h + 1) ∧ v ∈ Lay B r S h)) :=
  Iff.rfl

lemma lay_disj (h : ℕ) : Disjoint (Lay B r S h) (Lay B r S (h + 1)) := by
  rw [Finset.disjoint_left]; intro v h1 h2
  simp only [Lay, Finset.mem_filter] at h1 h2; omega

lemma pairG_degsum (h : ℕ) :
    ∑ u ∈ Lay B r S h ∪ Lay B r S (h + 1), dS (pairG B r S h) (Lay B r S h ∪ Lay B r S (h + 1)) u
      = 2 * eUp B r S h := by
  rw [Finset.sum_union (lay_disj B r S h)]
  have h1 : ∀ u ∈ Lay B r S h, dS (pairG B r S h) (Lay B r S h ∪ Lay B r S (h + 1)) u =
      ((Lay B r S (h + 1)).filter (B.Adj u)).card := by
    intro u hu; unfold dS; congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_union, pairG_adj]
    have hd := Finset.disjoint_left.mp (lay_disj B r S h)
    constructor
    · rintro ⟨_, hw, (⟨_, h2⟩ | ⟨h2, _⟩)⟩
      · exact ⟨h2, hw⟩
      · exact absurd hu (Finset.disjoint_right.mp (lay_disj B r S h) h2)
    · rintro ⟨h2, hw⟩; exact ⟨Or.inr h2, hw, Or.inl ⟨hu, h2⟩⟩
  have h2 : ∀ u ∈ Lay B r S (h + 1), dS (pairG B r S h) (Lay B r S h ∪ Lay B r S (h + 1)) u =
      ((Lay B r S h).filter (B.Adj u)).card := by
    intro u hu; unfold dS; congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_union, pairG_adj]
    constructor
    · rintro ⟨_, hw, (⟨h2, _⟩ | ⟨_, h2⟩)⟩
      · exact absurd h2 (Finset.disjoint_right.mp (lay_disj B r S h) hu)
      · exact ⟨h2, hw⟩
    · rintro ⟨h2, hw⟩; exact ⟨Or.inl h2, hw, Or.inr ⟨hu, h2⟩⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← eUp_comm]
  unfold eUp; ring

end Thm2


section Thm2b

variable {V : Type} [Fintype V] (B : SimpleGraph V) (r : V) (S : Finset V)
  (col : V → Bool) (hcol : ∀ u v, B.Adj u v → col u ≠ col v)
  (hsupp : ∀ u v, B.Adj u v → v ∈ S)
include hcol hsupp

lemma exists_dense_layer (hr : r ∈ S) (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : ∀ v ∈ S, μ ≤ dS B S v) :
    ∃ h, μ * ((Lay B r S h).card + (Lay B r S (h + 1)).card) ≤ 8 * eUp B r S h ∧
      (Lay B r S h).Nonempty ∧ (h = 0 ∨ 5 ^ (h - 1) ≤ S.card) := by
  have hex : ∃ h, μ * ((Lay B r S h).card + (Lay B r S (h + 1)).card) ≤ 8 * eUp B r S h := by
    by_contra hne
    push Not at hne
    have := layer_growth B r S col hcol hsupp hr μ hμ hdeg (S.card + 1)
      (fun j _ => by exact_mod_cast hne j) (S.card + 1) (by omega) le_rfl
    have h1 : (Lay B r S (S.card + 1)).card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : S.card < 5 ^ S.card := Nat.lt_pow_self (by norm_num)
    simp only [Nat.add_sub_cancel] at this
    omega
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, lay_zero B r S hr]; exact ⟨Finset.singleton_nonempty r, Or.inl rfl⟩
  · have := layer_growth B r S col hcol hsupp hr μ hμ hdeg (Nat.find hex)
      (fun j hj => by
        have := Nat.find_min hex hj
        push Not at this
        exact_mod_cast this) (Nat.find hex) hpos le_rfl
    refine ⟨?_, Or.inr (le_trans this.1 (Finset.card_le_card (Finset.filter_subset _ _)))⟩
    rw [← Finset.card_pos]
    have : 1 ≤ 5 ^ (Nat.find hex - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega

/-- Theorem 2 analogue: a dense layer pair with a longest path gives almost all even cycle
lengths `2c + 2e`, `c ≤ h`, `e ≤ s/3`, with `LP F ≤ 2s + 2` for a dense core `F`. -/
lemma thm2 (hr : r ∈ S) (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : ∀ v ∈ S, μ ≤ dS B S v) :
    ∃ h s : ℕ, ∃ F : SimpleGraph V, ∃ T : Finset V,
      (h = 0 ∨ 5 ^ (h - 1) ≤ S.card) ∧ F ≤ B ∧ T.Nonempty ∧ (∀ v ∈ T, (μ : ℝ) / 16 < dS F T v) ∧
      (∀ u v, F.Adj u v → v ∈ T) ∧ LP F ≤ 2 * s + 2 ∧
      (1 ≤ s → ∃ c m, 1 ≤ c ∧ c ≤ h ∧ 2 ≤ m ∧
        ∀ e, 1 ≤ e → 3 * e ≤ s → ¬ m ∣ e → 2 * c + 2 * e ∈ B.cycleLengths) := by
  obtain ⟨h, hden, hLne, hsize⟩ := exists_dense_layer B r S col hcol hsupp hr μ hμ hdeg
  set U := Lay B r S h ∪ Lay B r S (h + 1) with hU
  set Q := pairG B r S h with hQ
  have hUne : U.Nonempty := hLne.mono Finset.subset_union_left
  have hsum := pairG_degsum B r S h
  have hcond : 2 * ((μ : ℝ) / 16) * U.card ≤ ∑ u ∈ U, (dS Q U u : ℝ) := by
    rw [← Nat.cast_sum, hsum]
    have hc : U.card = (Lay B r S h).card + (Lay B r S (h + 1)).card :=
      Finset.card_union_of_disjoint (lay_disj B r S h)
    rw [hc]
    have : ((μ * ((Lay B r S h).card + (Lay B r S (h + 1)).card) : ℕ) : ℝ) ≤
        ((8 * eUp B r S h : ℕ) : ℝ) := by exact_mod_cast hden
    push_cast at this ⊢
    nlinarith [this]
  have hμpos : (0 : ℝ) < μ / 16 := by
    have : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
    positivity
  obtain ⟨T, hTne, hT⟩ := exists_dense_subset Q (μ / 16) hμpos U hUne hcond
  have hTU : ∀ v ∈ T, v ∈ U := by
    intro v hv
    have := lt_trans hμpos (hT v hv)
    have hpos : 0 < dS Q T v := by exact_mod_cast this
    unfold dS at hpos
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have hadj := (Finset.mem_filter.mp hw).2
    rw [hQ, pairG_adj] at hadj
    rcases hadj.2 with h1 | h1
    · exact Finset.mem_union_left _ h1.1
    · exact Finset.mem_union_right _ h1.1
  set F := restr Q T with hF
  have hFB : F ≤ B := fun u v huv => ((restr_le Q T) huv).1
  have hFT : ∀ u v, F.Adj u v → v ∈ T := restr_supported Q T
  have hFT' : ∀ u v, F.Adj u v → u ∈ T := fun u v huv => hFT v u huv.symm
  have hFdeg : ∀ v ∈ T, (μ : ℝ) / 16 < dS F T v := by
    intro v hv; rw [dS_restr Q T hv]; exact hT v hv
  obtain ⟨x, hx⟩ := hTne
  obtain ⟨u, v, p, hp, hpl⟩ := exists_LP F x
  set ℓ := LP F with hℓ
  have hvert : 1 ≤ ℓ → ∀ i, i ≤ ℓ → p.getVert i ∈ T := by
    intro h1 i hi
    rcases Nat.lt_or_ge i ℓ with h2 | h2
    · exact hFT' _ _ (p.adj_getVert_succ (by omega))
    · have := p.adj_getVert_succ (i := ℓ - 1) (by omega)
      rw [show ℓ - 1 + 1 = i by omega] at this
      exact hFT _ _ this
  set off := if p.getVert 0 ∈ Lay B r S h then 0 else 1 with hoff
  have hoff1 : off ≤ 1 := by simp only [hoff]; split_ifs <;> omega
  set s := (ℓ - off) / 2 with hs
  refine ⟨h, s, F, T, hsize, hFB, ⟨x, hx⟩, hFdeg, hFT, by omega, fun hs1 => ?_⟩
  have hℓ2 : 2 * s + off ≤ ℓ := by omega
  have hℓ1 : 1 ≤ ℓ := by omega
  let f : ℕ → V := fun i => p.getVert (i + off)
  have hfQ : ∀ i, i < 2 * s → Q.Adj (f i) (f (i + 1)) := by
    intro i hi
    have := p.adj_getVert_succ (i := i + off) (by omega)
    rw [show i + off + 1 = i + 1 + off by omega] at this
    exact ((restr_le Q T) this)
  have hfU : ∀ i, i ≤ 2 * s → f i ∈ U := fun i hi => hTU _ (hvert hℓ1 _ (by omega))
  have hdisj := Finset.disjoint_left.mp (lay_disj B r S h)
  have hf0 : f 0 ∈ Lay B r S h := by
    simp only [f, zero_add]
    by_cases h0 : p.getVert 0 ∈ Lay B r S h
    · have : off = 0 := by rw [hoff, if_pos h0]
      rw [this]; exact h0
    · have hoff' : off = 1 := by rw [hoff, if_neg h0]
      rw [hoff']
      have hadj := (restr_le Q T) (p.adj_getVert_succ (i := 0) (by omega))
      rw [hQ, pairG_adj] at hadj
      rcases hadj.2 with h1 | h1
      · exact absurd h1.1 h0
      · exact h1.2
  have halt : ∀ i, i ≤ 2 * s → (f i ∈ Lay B r S h ↔ Even i) := by
    intro i
    induction i with
    | zero => intro _; simp [hf0]
    | succ i ih =>
      intro hi
      have hadj := hfQ i (by omega)
      rw [hQ, pairG_adj] at hadj
      rw [Nat.even_add_one, ← ih (by omega)]
      rcases hadj.2 with h1 | h1
      · exact ⟨fun h2 => absurd h1.2 (hdisj h2), fun h2 => absurd h1.1 h2⟩
      · exact ⟨fun _ h3 => hdisj h3 h1.1, fun _ => h1.2⟩
  have hlevU : ∀ i, i ≤ 2 * s → h ≤ B.dist r (f i) := by
    intro i hi
    have := hfU i hi
    simp only [U, Finset.mem_union, Lay, Finset.mem_filter] at this
    omega
  have htop : ∀ i, i ≤ s → B.dist r (f (2 * i)) = h := by
    intro i hi
    have := (halt (2 * i) (by omega)).mpr (even_two_mul i)
    simp only [Lay, Finset.mem_filter] at this
    exact this.2.2
  have hinj : ∀ i j, i ≤ 2 * s → j ≤ 2 * s → f i = f j → i = j := by
    intro i j hi hj e
    have := hp.getVert_injOn (show i + off ∈ {k | k ≤ p.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show j + off ∈ {k | k ≤ p.length} by simp only [Set.mem_setOf_eq]; omega) e
    omega
  have hh1 : 1 ≤ h := by
    by_contra h0
    have h0' : h = 0 := by omega
    have r0 : f 0 = r := by
      have := (halt 0 (by omega)).mpr (by decide)
      rw [h0', lay_zero B r S hr] at this
      exact Finset.mem_singleton.mp this
    have r2 : f 2 = r := by
      have := (halt 2 (by omega)).mpr (by decide)
      rw [h0', lay_zero B r S hr] at this
      exact Finset.mem_singleton.mp this
    have := hinj 2 0 (by omega) (by omega) (r2.trans r0.symm)
    omega
  have hroot : ∀ i, i ≤ s → (bpar B r)^[h] (f (2 * i)) = (bpar B r)^[h] (f 0) := by
    intro i hi
    have h0 := htop 0 (by omega)
    simp only [mul_zero] at h0
    have e1 := bpar_iter_root B r (f (2 * i)) (by rw [htop i hi]; exact hh1)
    have e2 := bpar_iter_root B r (f 0) (by rw [h0]; exact hh1)
    rw [htop i hi] at e1
    rw [h0] at e2
    rw [e1, e2]
  obtain ⟨c, m, hc1, hch, hm, hcyc⟩ := engine (bpar_isParent B r) f s h hs1
    (fun i hi => (hfQ i hi).1) hinj hlevU htop h le_rfl hroot
  exact ⟨c, m, hc1, hch, hm, hcyc⟩

end Thm2b



section MaxCut

variable {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V)

/-- crossing degree of `v` for the colouring `col` -/
def cross (col : V → Bool) (v : V) : ℕ := (S.filter (fun u => G.Adj v u ∧ col u ≠ col v)).card

/-- same-colour degree -/
def same (col : V → Bool) (v : V) : ℕ := (S.filter (fun u => G.Adj v u ∧ col u = col v)).card

lemma cross_add_same (col : V → Bool) (v : V) : cross G S col v + same G S col v = dS G S v := by
  unfold cross same dS
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · rw [Finset.disjoint_left]; intro u h1 h2
    simp only [Finset.mem_filter] at h1 h2; exact h1.2.2 h2.2.2

omit [Fintype V] in
lemma cross_flip_self (col : V → Bool) (v : V) :
    cross G S (Function.update col v (!col v)) v = same G S col v := by
  unfold cross same; congr 1; ext u
  simp only [Finset.mem_filter, Function.update_self]
  constructor
  · rintro ⟨hu, hadj, hc⟩
    have huv : u ≠ v := fun h => G.loopless.irrefl _ (h ▸ hadj)
    rw [Function.update_of_ne huv] at hc
    refine ⟨hu, hadj, ?_⟩
    cases h1 : col u <;> cases h2 : col v <;> simp_all
  · rintro ⟨hu, hadj, hc⟩
    have huv : u ≠ v := fun h => G.loopless.irrefl _ (h ▸ hadj)
    rw [Function.update_of_ne huv]
    refine ⟨hu, hadj, ?_⟩
    cases h1 : col u <;> cases h2 : col v <;> simp_all

omit [Fintype V] in
lemma card_filter_split (S : Finset V) (v : V) (P : V → Prop) [DecidablePred P] :
    (S.filter P).card = ((S.erase v).filter P).card + (if v ∈ S ∧ P v then 1 else 0) := by
  by_cases hv : v ∈ S
  · have : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    conv_lhs => rw [this]
    rw [Finset.filter_insert]
    by_cases hP : P v
    · rw [if_pos hP, Finset.card_insert_of_notMem (by simp), if_pos ⟨hv, hP⟩]
    · rw [if_neg hP, if_neg (fun h => hP h.2)]; simp
  · rw [Finset.erase_eq_of_notMem hv]; simp [hv]

lemma cross_flip_other (col : V → Bool) (v w : V) (hw : w ≠ v) :
    (cross G S (Function.update col v (!col v)) w : ℤ) = cross G S col w +
      (if v ∈ S ∧ G.Adj w v ∧ col v = col w then 1 else 0) -
      (if v ∈ S ∧ G.Adj w v ∧ col v ≠ col w then 1 else 0) := by
  unfold cross
  rw [card_filter_split S v, card_filter_split S v]
  have hrest : ((S.erase v).filter (fun u => G.Adj w u ∧ Function.update col v (!col v) u ≠
      Function.update col v (!col v) w)) = ((S.erase v).filter (fun u => G.Adj w u ∧ col u ≠ col w)) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨huv, hu⟩, h⟩
      rw [Function.update_of_ne huv, Function.update_of_ne hw] at h; exact ⟨⟨huv, hu⟩, h⟩
    · rintro ⟨⟨huv, hu⟩, h⟩
      rw [Function.update_of_ne huv, Function.update_of_ne hw]; exact ⟨⟨huv, hu⟩, h⟩
  rw [hrest]
  simp only [Function.update_self, Function.update_of_ne hw]
  by_cases hv : v ∈ S <;> by_cases ha : G.Adj w v <;> cases h1 : col v <;> cases h2 : col w <;>
    simp [hv, ha, h1, h2]

lemma maxcut : ∃ col : V → Bool, ∀ v ∈ S, dS G S v ≤ 2 * cross G S col v := by
  obtain ⟨col, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool))
    (fun col => ∑ w ∈ S, cross G S col w) Finset.univ_nonempty
  refine ⟨col, fun v hv => ?_⟩
  by_contra hlt
  push Not at hlt
  have hcs := cross_add_same G S col v
  set col' := Function.update col v (!col v)
  have h1 := hmax col' (Finset.mem_univ _)
  -- compute the potential of col'
  have hsum : (∑ w ∈ S, (cross G S col' w : ℤ)) =
      ∑ w ∈ S, (cross G S col w : ℤ) + 2 * ((same G S col v : ℤ) - cross G S col v) := by
    rw [← Finset.add_sum_erase S _ hv, ← Finset.add_sum_erase S (fun w => (cross G S col w : ℤ)) hv]
    rw [cross_flip_self]
    rw [Finset.sum_congr rfl (fun w hw => cross_flip_other G S col v w (Finset.ne_of_mem_erase hw))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have e1 : ∑ w ∈ S.erase v, (if v ∈ S ∧ G.Adj w v ∧ col v = col w then (1 : ℤ) else 0) =
        same G S col v := by
      rw [Finset.sum_boole]; unfold same
      congr 1; congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_erase]; constructor
      · rintro ⟨⟨_, hu⟩, -, h2, h3⟩; exact ⟨hu, h2.symm, h3.symm⟩
      · rintro ⟨hu, h2, h3⟩
        refine ⟨⟨fun h => ?_, hu⟩, hv, h2.symm, h3.symm⟩
        subst h; exact G.loopless.irrefl _ h2
    have e2 : ∑ w ∈ S.erase v, (if v ∈ S ∧ G.Adj w v ∧ col v ≠ col w then (1 : ℤ) else 0) =
        cross G S col v := by
      rw [Finset.sum_boole]; unfold cross
      congr 1; congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_erase]; constructor
      · rintro ⟨⟨_, hu⟩, -, h2, h3⟩; exact ⟨hu, h2.symm, Ne.symm h3⟩
      · rintro ⟨hu, h2, h3⟩
        refine ⟨⟨fun h => ?_, hu⟩, hv, h2.symm, Ne.symm h3⟩
        subst h; exact G.loopless.irrefl _ h2
    rw [e1, e2]
    ring
  have h1' : ((∑ w ∈ S, cross G S col' w : ℕ) : ℤ) ≤ ((∑ w ∈ S, cross G S col w : ℕ) : ℤ) := by
    exact_mod_cast h1
  push_cast at h1'
  rw [hsum] at h1'
  have : (same G S col v : ℤ) > cross G S col v := by
    have : (dS G S v : ℤ) = cross G S col v + same G S col v := by exact_mod_cast hcs.symm
    have h2 : (2 * cross G S col v : ℤ) < dS G S v := by exact_mod_cast hlt
    linarith
  linarith

/-- the bipartite subgraph of crossing edges -/
def bip (col : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ col u ≠ col v
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

omit [Fintype V] in
lemma bip_le (col : V → Bool) : bip G col ≤ G := fun _ _ h => h.1

lemma dS_bip (col : V → Bool) (v : V) : dS (bip G col) S v = cross G S col v := by
  unfold dS cross; congr 1; ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, h⟩; exact ⟨hu, h.1, Ne.symm h.2⟩
  · rintro ⟨hu, h1, h2⟩; exact ⟨hu, h1, Ne.symm h2⟩

end MaxCut


section LPge

variable {V : Type} [Fintype V]

/-- `(F, T)` is a `λ`-dense pair: `F` lives on `T` and has minimum degree `≥ λ` there. -/
def DensePair (F : SimpleGraph V) (T : Finset V) (lam : ℝ) : Prop :=
  T.Nonempty ∧ (∀ v ∈ T, lam ≤ dS F T v) ∧ (∀ u v, F.Adj u v → v ∈ T)

/-- the end of a longest path has all its neighbours on the path -/
lemma nbrs_on_longest (F : SimpleGraph V) {u v : V} (p : F.Walk u v) (hp : p.IsPath)
    (hl : p.length = LP F) {w : V} (hw : F.Adj v w) : w ∈ p.support := by
  by_contra hns
  have := le_LP F (p.concat hw) (hp.concat hns hw)
  rw [Walk.length_concat] at this; omega

lemma LP_ge (F : SimpleGraph V) (T : Finset V) (lam : ℝ) (hlam : 0 < lam)
    (hD : DensePair F T lam) : lam ≤ LP F := by
  obtain ⟨⟨x, hx⟩, hdeg, hsupp⟩ := hD
  obtain ⟨u, v, p, hp, hpl⟩ := exists_LP F x
  have hdegpos : ∀ y ∈ T, ∃ w, F.Adj y w := by
    intro y hy
    have h1 := lt_of_lt_of_le hlam (hdeg y hy)
    have : 0 < dS F T y := by exact_mod_cast h1
    unfold dS at this
    obtain ⟨w, hw⟩ := Finset.card_pos.mp this
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  have hℓ : 1 ≤ LP F := by
    obtain ⟨w, hw⟩ := hdegpos x hx
    have := le_LP F (Walk.cons hw Walk.nil) (by simp [hw.ne])
    simpa using this
  have hv : v ∈ T := by
    have := p.adj_getVert_succ (i := LP F - 1) (by omega)
    rw [show LP F - 1 + 1 = p.length by omega, Walk.getVert_length] at this
    exact hsupp _ _ this
  have hsub : T.filter (F.Adj v) ⊆ p.support.toFinset.erase v := by
    intro w hw
    have hadj := (Finset.mem_filter.mp hw).2
    rw [Finset.mem_erase, List.mem_toFinset]
    exact ⟨hadj.ne.symm, nbrs_on_longest F p hp hpl hadj⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), List.toFinset_card_of_nodup hp.support_nodup,
    Walk.length_support] at hc
  have := hdeg v hv
  unfold dS at this
  have : (dS F T v : ℝ) ≤ LP F := by unfold dS; exact_mod_cast (by omega)
  linarith [hdeg v hv]

end LPge




section Shrink

variable {V : Type} [Fintype V] (F : SimpleGraph V)

lemma list_len_le_LP (L : List V) (hc : L.IsChain F.Adj) (hn : L.Nodup) :
    L.length ≤ LP F + 1 := by
  by_cases h : L = []
  · simp [h]
  have hne := h
  set x0 := L.head hne
  let g : ℕ → V := fun i => L.getD i x0
  have hlen : 1 ≤ L.length := by
    rcases L with _ | ⟨a, l⟩
    · exact absurd rfl hne
    · simp
  have hadj : ∀ i, i < L.length - 1 → F.Adj (g i) (g (i + 1)) := by
    intro i hi
    have := (List.isChain_iff_getElem.mp hc) i (by omega)
    simp only [g, List.getD_eq_getElem _ _ (show i < L.length by omega),
      List.getD_eq_getElem _ _ (show i + 1 < L.length by omega)]
    exact this
  obtain ⟨p, hp, hpl⟩ := walk_of_fun F g (L.length - 1) hadj
  have hsupp : (List.range (L.length - 1 + 1)).map g = L := by
    rw [show L.length - 1 + 1 = L.length by omega]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, g]
    rw [List.getD_eq_getElem _ _ h2]
  have hpath : p.IsPath := by rw [Walk.isPath_def, hp, hsupp]; exact hn
  have := le_LP F p hpath
  omega

/-- valid extensions of a prefix `R` avoiding `Y` -/
def VExt (R : List V) (Y : Finset V) (L : List V) : Prop :=
  R <+: L ∧ L.IsChain F.Adj ∧ L.Nodup ∧ ∀ x ∈ L, x ∉ Y

lemma exists_longest_ext (R : List V) (Y : Finset V) (hR : VExt F R Y R) :
    ∃ L, VExt F R Y L ∧ ∀ L', VExt F R Y L' → L'.length ≤ L.length := by
  have hb : ∀ L, VExt F R Y L → L.length ≤ Fintype.card V := fun L hL =>
    hL.2.2.1.length_le_card
  let P : ℕ → Prop := fun n => ∃ L, VExt F R Y L ∧ L.length = n
  have hP : P R.length := ⟨R, hR, rfl⟩
  have hle : R.length ≤ Fintype.card V := hb R hR
  obtain ⟨L, hL, hLl⟩ := Nat.findGreatest_spec (P := P) hle hP
  refine ⟨L, hL, fun L' hL' => ?_⟩
  rw [hLl]
  exact Nat.le_findGreatest (hb L' hL') ⟨L', hL', rfl⟩

/-- one step of the GKS Lemma 4 construction -/
lemma shrink_step (T : Finset V) (hsupp : ∀ a b, F.Adj a b → b ∈ T)
    (R : List V) (Y : Finset V) (hR : VExt F R Y R) (hne : R ≠ []) (hRT : ∀ x ∈ R, x ∈ T) :
    ∃ R' : List V, ∃ y : V, y ∉ Y ∧ VExt F R' (insert y Y) R' ∧ R.length ≤ R'.length + 1 ∧
      (∀ x ∈ R, x ∈ R' ∨ x = y) ∧ (∀ x ∈ R', x ∈ T) ∧ y ∈ T ∧
      (∀ w, F.Adj y w → w ∈ R' ∨ w ∈ Y) ∧ R'.length + 1 ≤ LP F + 1 := by
  obtain ⟨L, hL, hmax⟩ := exists_longest_ext F R Y hR
  obtain ⟨hpre, hch, hnd, hY⟩ := hL
  have hLne : L ≠ [] := by
    intro h; rw [h] at hpre; exact hne (List.prefix_nil.mp hpre)
  set y := L.getLast hLne
  set R' := L.dropLast
  have hLeq : L = R' ++ [y] := (List.dropLast_append_getLast hLne).symm
  have hyL : y ∈ L := List.getLast_mem hLne
  have hyR' : y ∉ R' := by
    intro h
    have := hnd
    rw [hLeq, List.nodup_append] at this
    exact this.2.2 y h y (by simp) rfl
  have hLT : ∀ x ∈ L, x ∈ T := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    by_cases hiR : i < R.length
    · rw [← hpre.getElem hiR]; exact hRT _ (List.getElem_mem _)
    · have hpos : 0 < R.length := List.length_pos_of_ne_nil hne
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := (List.isChain_iff_getElem.mp hch) j (by omega)
      exact hsupp _ _ this
  refine ⟨R', y, hY y hyL, ⟨List.prefix_refl _, hch.dropLast, hnd.sublist (List.dropLast_sublist _), ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hyR' (h ▸ hx)
    · exact hY x (List.mem_of_mem_dropLast hx) h
  · have := hpre.length_le
    have h2 : L.length = R'.length + 1 := by rw [hLeq]; simp
    omega
  · intro x hx
    have := hpre.subset hx
    rw [hLeq, List.mem_append, List.mem_singleton] at this
    exact this
  · intro x hx; exact hLT x (List.mem_of_mem_dropLast hx)
  · exact hLT y hyL
  · intro w hw
    by_cases hwY : w ∈ Y
    · right; exact hwY
    left
    by_contra hwR'
    have hwy : w ≠ y := fun h => F.loopless.irrefl y (h ▸ hw)
    have hwL : w ∉ L := by
      rw [hLeq, List.mem_append, List.mem_singleton]; push Not; exact ⟨hwR', hwy⟩
    have hext : VExt F R Y (L ++ [w]) := by
      refine ⟨hpre.trans (List.prefix_append _ _), ?_, ?_, ?_⟩
      · apply hch.append (List.isChain_singleton w)
        intro x hx z hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        subst hz
        rw [List.getLast?_eq_some_getLast hLne, Option.mem_def, Option.some.injEq] at hx
        rw [← hx]; exact hw
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton w, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        exact hwL (hb ▸ hab ▸ ha)
      · intro x hx
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hY x hx
        · exact hwY
    have := hmax _ hext
    simp at this
  · have := list_len_le_LP F L hch hnd
    have h2 : L.length = R'.length + 1 := by rw [hLeq]; simp
    omega

/-- GKS Lemma 4 (iterated longest extensions). -/
lemma lemma4 (T : Finset V) (hsupp : ∀ a b, F.Adj a b → b ∈ T) (hLP : 1 ≤ LP F) :
    ∀ t, t ≤ LP F + 1 → ∃ R : List V, ∃ Y : Finset V, VExt F R Y R ∧ Y.card = t ∧
      LP F + 1 ≤ R.length + t ∧ R.length ≤ LP F + 1 ∧ (∀ x ∈ R, x ∈ T) ∧ (∀ y ∈ Y, y ∈ T) ∧
      (∀ y ∈ Y, ∀ w, F.Adj y w → w ∈ R ∨ w ∈ Y) := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨x⟩ : Nonempty V := by
      by_contra h; rw [not_nonempty_iff] at h
      have : LP F = 0 := by
        unfold LP; rw [Fintype.card_eq_zero]; simp
      omega
    obtain ⟨u, v, p, hp, hpl⟩ := exists_LP F x
    have hsl : p.support.length = LP F + 1 := by rw [Walk.length_support, hpl]
    refine ⟨p.support, ∅, ⟨List.prefix_refl _, p.isChain_adj_support, hp.support_nodup, by simp⟩,
      by simp, by omega, by omega, ?_, by simp, by simp⟩
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hc := List.isChain_iff_getElem.mp p.isChain_adj_support
    by_cases hi0 : i = 0
    · subst hi0
      have := hc 0 (by omega)
      exact hsupp _ _ this.symm
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := hc j (by omega)
      exact hsupp _ _ this
  | succ t ih =>
    intro ht
    obtain ⟨R, Y, hR, hY, hl1, hl2, hRT, hYT, hnb⟩ := ih (by omega)
    have hne : R ≠ [] := by
      intro h; rw [h] at hl1; simp at hl1; omega
    obtain ⟨R', y, hyY, hR', hlen, hsub, hR'T, hyT, hynb, hR'l⟩ :=
      shrink_step F T hsupp R Y hR hne hRT
    refine ⟨R', insert y Y, hR', by rw [Finset.card_insert_of_notMem hyY, hY], by omega, by omega,
      hR'T, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hyT
      · exact hYT z hz
    · intro z hz w hw
      rw [Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · rcases hynb w hw with h | h
        · left; exact h
        · right; right; exact h
      · rcases hnb z hz w hw with h | h
        · rcases hsub w h with h' | h'
          · left; exact h'
          · right; left; exact h'
        · right; right; exact h

/-- Shrinking (GKS Corollary 4): a dense pair contains a dense pair on `≤ 2 LP + 2` vertices. -/
lemma shrink (T : Finset V) (lam : ℝ) (hlam : 0 < lam) (hD : DensePair F T lam) :
    ∃ F' : SimpleGraph V, ∃ T' : Finset V, F' ≤ F ∧ DensePair F' T' (lam / 4) ∧
      T'.card ≤ 2 * LP F + 2 := by
  have hLP := LP_ge F T lam hlam hD
  obtain ⟨hTne, hdeg, hsupp⟩ := hD
  have hLP1 : 1 ≤ LP F := by
    have : (0 : ℝ) < LP F := lt_of_lt_of_le hlam hLP
    exact_mod_cast this
  obtain ⟨R, Y, -, hYc, -, hRl, -, hYT, hnb⟩ := lemma4 F T hsupp hLP1 (LP F + 1) le_rfl
  set W := R.toFinset ∪ Y with hW
  have hWc : W.card ≤ 2 * LP F + 2 := by
    have := Finset.card_union_le R.toFinset Y
    have := List.toFinset_card_le R
    have : W.card = (R.toFinset ∪ Y).card := rfl
    omega
  set H := restr F W with hH
  have hYdeg : ∀ y ∈ Y, lam ≤ dS H W y := by
    intro y hy
    have hyW : y ∈ W := Finset.mem_union_right _ hy
    rw [hH, dS_restr F W hyW]
    refine le_trans (hdeg y (hYT y hy)) ?_
    unfold dS
    have : T.filter (F.Adj y) ⊆ W.filter (F.Adj y) := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨?_, hadj⟩
      rcases hnb y hy w hadj with h | h
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
      · exact Finset.mem_union_right _ h
    exact_mod_cast Finset.card_le_card this
  have hWne : W.Nonempty := by
    have : 0 < Y.card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp this
    exact ⟨y, Finset.mem_union_right _ hy⟩
  have hsum : 2 * (lam / 4) * W.card ≤ ∑ u ∈ W, (dS H W u : ℝ) := by
    have h1 : ∑ u ∈ Y, (dS H W u : ℝ) ≤ ∑ u ∈ W, (dS H W u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun _ _ _ => by positivity)
    have h2 : (Y.card : ℝ) * lam ≤ ∑ u ∈ Y, (dS H W u : ℝ) := by
      have := Finset.card_nsmul_le_sum Y (fun u => (dS H W u : ℝ)) lam hYdeg
      rwa [nsmul_eq_mul] at this
    have h3 : (W.card : ℝ) ≤ 2 * Y.card := by
      have : W.card ≤ 2 * Y.card := by omega
      exact_mod_cast this
    nlinarith
  obtain ⟨T', hT'ne, hT'⟩ := exists_dense_subset H (lam / 4) (by positivity) W hWne hsum
  have hT'W : ∀ v ∈ T', v ∈ W := by
    intro v hv
    have := lt_trans (by positivity : (0 : ℝ) < lam / 4) (hT' v hv)
    have hpos : 0 < dS H T' v := by exact_mod_cast this
    unfold dS at hpos
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    exact ((restr_adj F W v w).mp (Finset.mem_filter.mp hw).2).2.1
  refine ⟨restr H T', T', le_trans (restr_le H T') (restr_le F W), ⟨hT'ne, ?_, restr_supported H T'⟩,
    le_trans (Finset.card_le_card hT'W) hWc⟩
  intro v hv
  rw [dS_restr H T' hv]; exact (hT' v hv).le

end Shrink



section Chain

variable {V : Type} [Fintype V]

omit [Fintype V] in
lemma DensePair.mono [Fintype V] {F : SimpleGraph V} {T : Finset V} {lam lam' : ℝ} (h : lam' ≤ lam)
    (hD : DensePair F T lam) : DensePair F T lam' :=
  ⟨hD.1, fun v hv => le_trans h (hD.2.1 v hv), hD.2.2⟩

/-- a dense pair minimising the longest path -/
lemma realize (G : SimpleGraph V) (lam : ℝ) (hex : ∃ F T, F ≤ G ∧ DensePair F T lam) :
    ∃ F T, F ≤ G ∧ DensePair F T lam ∧
      ∀ F' T', F' ≤ G → DensePair F' T' lam → LP F ≤ LP F' := by
  have hP : ∃ n, ∃ F T, F ≤ G ∧ DensePair F T lam ∧ LP F ≤ n := by
    obtain ⟨F, T, h1, h2⟩ := hex; exact ⟨LP F, F, T, h1, h2, le_rfl⟩
  obtain ⟨F, T, h1, h2, h3⟩ := Nat.find_spec hP
  refine ⟨F, T, h1, h2, fun F' T' h1' h2' => le_trans h3 (Nat.find_min' hP ⟨F', T', h1', h2', le_rfl⟩)⟩

lemma wAbove_anti (G : SimpleGraph V) {A B : ℕ} (h : A ≤ B) : wAbove G B ≤ wAbove G A := by
  unfold wAbove
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha; simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩
  · intro _ _ _; positivity

/-- One round: shrink, max-cut, BFS engine. -/
lemma round (G : SimpleGraph V) (lam : ℝ) (hlam : 0 < lam) (F1 : SimpleGraph V) (T1 : Finset V)
    (hF1 : F1 ≤ G) (hD1 : DensePair F1 T1 lam) (D : ℕ) (hD : 1 ≤ D) :
    (1 / 4 : ℝ) * Real.log D ≤ W G ∨ ∃ h : ℕ, (h = 0 ∨ 5 ^ (h - 1) ≤ 2 * LP F1 + 2) ∧
      ∃ F T, F ≤ G ∧ DensePair F T (lam / 128) ∧ LP F ≤ 6 * (h + 2) * D := by
  obtain ⟨F2, T2, hF2, hD2, hT2⟩ := shrink F1 T1 lam hlam hD1
  obtain ⟨⟨r, hr⟩, hdeg2, hsupp2⟩ := hD2
  obtain ⟨col, hcol⟩ := maxcut F2 T2
  set B := bip F2 col with hB
  set μ := ⌈lam / 8⌉₊ with hμ
  have hμ1 : 1 ≤ μ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hdegB : ∀ v ∈ T2, μ ≤ dS B T2 v := by
    intro v hv
    rw [hB, dS_bip]
    apply Nat.ceil_le.mpr
    have h1 := hdeg2 v hv
    have h2 : (dS F2 T2 v : ℝ) ≤ 2 * cross F2 T2 col v := by exact_mod_cast hcol v hv
    linarith
  have hcolB : ∀ u v, B.Adj u v → col u ≠ col v := fun u v h => h.2
  have hsuppB : ∀ u v, B.Adj u v → v ∈ T2 := fun u v h => hsupp2 u v h.1
  have hBG : B ≤ G := le_trans (bip_le F2 col) (le_trans hF2 hF1)
  obtain ⟨h, s, F, T, hsize, hFB, hTne, hFdeg, hFsupp, hLP, hcyc⟩ :=
    thm2 B r T2 col hcolB hsuppB hr μ hμ1 hdegB
  have hμlam : lam / 128 ≤ (μ : ℝ) / 16 := by
    have := Nat.le_ceil (lam / 8); rw [← hμ] at this; linarith
  by_cases hsucc : 3 * ((h + 2) * D) ≤ s
  · left
    obtain ⟨c, m, hc1, hch, hm, hcy⟩ := hcyc (by nlinarith)
    set E2 := s / 3
    have hE2 : (h + 2) * D ≤ E2 := by omega
    have hbw := block_weight (CF G) c m 1 E2 hm le_rfl (by nlinarith) (by
      intro e he1 he2 hme
      have hmem := cycleLengths_mono hBG (hcy e he1 (by omega) hme)
      simp only [CF, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (cycleLengths_le_card G hmem), hmem⟩)
    have hsub : ∑ a ∈ (CF G).filter (2 * c + 2 * 1 ≤ ·), (1 : ℝ) / a ≤ W G := by
      unfold W
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have hlog : Real.log D ≤ Real.log (((c + E2 + 1 : ℕ) : ℝ) / (c + 1 + 1 : ℕ)) := by
      apply Real.log_le_log (by exact_mod_cast hD)
      have hnum : (((c + 1 + 1) * D : ℕ) : ℝ) ≤ ((c + E2 + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show (c + 1 + 1) * D ≤ c + E2 + 1 by nlinarith)
      rw [le_div_iff₀ (by positivity), mul_comm]
      push_cast at hnum ⊢; linarith
    linarith
  · right
    refine ⟨h, ?_, F, T, le_trans hFB hBG, ⟨hTne, fun v hv => le_trans hμlam (hFdeg v hv).le, hFsupp⟩,
      by push Not at hsucc; nlinarith⟩
    rcases hsize with h0 | h0
    · left; exact h0
    · right; exact le_trans h0 hT2

end Chain



section MLproof

lemma sq_le_five_pow (u : ℕ) : u ^ 2 ≤ 5 ^ u := by
  induction u with
  | zero => simp
  | succ u ih =>
    have h1 : u < 5 ^ u := Nat.lt_pow_self (by norm_num)
    have e1 : (u + 1) ^ 2 = u ^ 2 + 2 * u + 1 := by ring
    have e2 : 5 ^ (u + 1) = 5 * 5 ^ u := by ring
    omega

lemma arith (K1 D h h' P1 d : ℕ) (hK1 : 1 ≤ K1) (hD1 : 1 ≤ D)
    (hDbig : 768 * K1 * 10000000 ≤ D ^ 4) (hD8 : D ^ 8 ≤ d) (hd : d ≤ 768 * K1 * ((h + 2) * D))
    (hh' : h' = 0 ∨ 5 ^ (h' - 1) ≤ 12 * (h + 2) * D + 2) (hh : h = 0 ∨ 5 ^ (h - 1) ≤ 2 * P1 + 2) :
    12 * (h' + 2) * D + 2 ≤ Nat.log 2 P1 / 64 := by
  set X := h + 2 with hX
  have s1 : D ^ 7 ≤ 768 * K1 * X := by
    have : D * D ^ 7 ≤ D * (768 * K1 * X) := by
      calc D * D ^ 7 = D ^ 8 := by ring
        _ ≤ d := hD8
        _ ≤ 768 * K1 * (X * D) := hd
        _ = D * (768 * K1 * X) := by ring
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have s2 : 10000000 * D ^ 3 ≤ X := by
    have : (768 * K1) * (10000000 * D ^ 3) ≤ (768 * K1) * X := by
      calc (768 * K1) * (10000000 * D ^ 3) = (768 * K1 * 10000000) * D ^ 3 := by ring
        _ ≤ D ^ 4 * D ^ 3 := Nat.mul_le_mul_right _ hDbig
        _ = D ^ 7 := by ring
        _ ≤ 768 * K1 * X := s1
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have hD3 : D ≤ D ^ 3 := Nat.le_self_pow (by norm_num) D
  have hD3' : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD1
  have hh2 : 2 ≤ h := by omega
  have hP : 5 ^ (h - 1) ≤ 2 * P1 + 2 := by
    rcases hh with h0 | h0
    · omega
    · exact h0
  have hlog : 2 * h - 4 ≤ Nat.log 2 P1 := by
    have h4 : 4 ^ (h - 1) ≤ 5 ^ (h - 1) := Nat.pow_le_pow_left (by norm_num) _
    have e1 : 4 ^ (h - 1) = 2 ^ (2 * h - 4) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1; omega
    have hp : 2 ^ (2 * h - 4) ≤ P1 := by
      have : 1 ≤ 2 ^ (2 * h - 4) := Nat.one_le_two_pow
      omega
    have hP1 : P1 ≠ 0 := by
      have : 1 ≤ 2 ^ (2 * h - 4) := Nat.one_le_two_pow
      omega
    exact Nat.le_log_of_pow_le (by norm_num) hp
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hXD : 10000000 * D ≤ X := le_trans (Nat.mul_le_mul_left _ hD3) s2
  rcases Nat.eq_zero_or_pos h' with h0 | hpos
  · subst h0; omega
  · have h5 : 5 ^ (h' - 1) ≤ 12 * X * D + 2 := by
      rcases hh' with h0 | h0
      · omega
      · exact h0
    set u := h' - 1 with hu
    have hu2 := sq_le_five_pow u
    have key : (768 * u * D) ^ 2 ≤ X ^ 2 := by
      have a1 : u ^ 2 ≤ 12 * X * D + 2 := le_trans hu2 h5
      have a2 : (768 * u * D) ^ 2 = 589824 * (u ^ 2 * D ^ 2) := by ring
      have a3 : u ^ 2 * D ^ 2 ≤ (12 * X * D + 2) * D ^ 2 := Nat.mul_le_mul_right _ a1
      have a4 : (12 * X * D + 2) * D ^ 2 ≤ 14 * X * D ^ 3 := by
        have : 2 * D ^ 2 ≤ 2 * X * D ^ 3 := by
          have : D ^ 2 ≤ D ^ 3 := Nat.pow_le_pow_right hD1 (by norm_num)
          nlinarith
        nlinarith
      have a5 : 589824 * (14 * X * D ^ 3) ≤ X ^ 2 := by
        have : 589824 * 14 * D ^ 3 ≤ X := by omega
        nlinarith
      nlinarith
    have key' : 768 * u * D ≤ X := by
      by_contra hc; push Not at hc
      have := Nat.pow_lt_pow_left hc (show 2 ≠ 0 by norm_num)
      omega
    have : h' = u + 1 := by omega
    rw [this]
    have e : (12 * (u + 1 + 2) * D + 2) * 64 = 768 * (u * D) + 2304 * D + 128 := by ring
    rw [e]
    have e2 : 768 * u * D = 768 * (u * D) := by ring
    rw [e2] at key'
    generalize u * D = Z at key' ⊢
    omega

/-- GKS Theorem 1 (Corollary 1), the remaining input. -/
def T1stmt : Prop :=
  ∃ c1 : ℕ, ∃ K1 : ℕ, 1 ≤ K1 ∧ ∃ w1 > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (d : ℕ), S.Nonempty → c1 ≤ d → (∀ v ∈ S, d ≤ dS G S v) →
    (∀ u v, G.Adj u v → v ∈ S) → ∀ P : ℕ,
    (∀ F T, F ≤ G → DensePair F T ((d : ℝ) / K1) → P ≤ LP F) →
    w1 ≤ wAbove G (Nat.log 2 P / 64)

lemma ML_of_T1 (hT1 : T1stmt) : ML := by
  obtain ⟨c1, K1, hK1, w1, hw1, hT1⟩ := hT1
  set D0 := 768 * K1 * 10000000 with hD0
  have hD0pos : 2 ≤ D0 := by omega
  set d0 := max (max c1 (D0 ^ 8)) (2 * (65536 * K1)) with hd0
  have hd01 : 1 ≤ d0 := le_trans (Nat.one_le_pow _ _ (by omega)) (le_trans (le_max_right c1 _)
    (le_max_left _ _))
  refine ⟨d0, hd01, 65536 * K1, by omega, le_max_right _ _, w1, hw1, 1 / 64, by norm_num, ?_⟩
  intro V _ G S d hS hd hdeg hsupp
  have hc1 : c1 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hdD0 : D0 ^ 8 ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  set D := Nat.sqrt (Nat.sqrt (Nat.sqrt d)) with hDdef
  have hD8 : D ^ 8 ≤ d := by
    have h1 := Nat.sqrt_le' (Nat.sqrt (Nat.sqrt d))
    have h2 := Nat.sqrt_le' (Nat.sqrt d)
    have h3 := Nat.sqrt_le' d
    calc D ^ 8 = ((D ^ 2) ^ 2) ^ 2 := by ring
      _ ≤ ((Nat.sqrt (Nat.sqrt d)) ^ 2) ^ 2 := by gcongr
      _ ≤ (Nat.sqrt d) ^ 2 := by gcongr
      _ ≤ d := h3
  have hDD0 : D0 ≤ D := by
    rw [hDdef, Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt']
    calc ((D0 ^ 2) ^ 2) ^ 2 = D0 ^ 8 := by ring
      _ ≤ d := hdD0
  have hD2 : 2 ≤ D := le_trans hD0pos hDD0
  have hdD : d ≤ D ^ 16 := by
    have h1 := Nat.lt_succ_sqrt' (Nat.sqrt (Nat.sqrt d))
    have h2 := Nat.lt_succ_sqrt' (Nat.sqrt d)
    have h3 := Nat.lt_succ_sqrt' d
    have e1 : Nat.sqrt (Nat.sqrt d) < (D + 1) ^ 2 := h1
    have e2 : Nat.sqrt d < ((D + 1) ^ 2) ^ 2 := by
      calc Nat.sqrt d < (Nat.sqrt (Nat.sqrt d) + 1) ^ 2 := h2
        _ ≤ ((D + 1) ^ 2) ^ 2 := by gcongr; omega
    have e3 : d < (((D + 1) ^ 2) ^ 2) ^ 2 := by
      calc d < (Nat.sqrt d + 1) ^ 2 := h3
        _ ≤ (((D + 1) ^ 2) ^ 2) ^ 2 := by gcongr; omega
    have e4 : (((D + 1) ^ 2) ^ 2) ^ 2 ≤ D ^ 16 := by
      calc (((D + 1) ^ 2) ^ 2) ^ 2 = (D + 1) ^ 8 := by ring
        _ ≤ (2 * D) ^ 8 := by gcongr; omega
        _ = 256 * D ^ 8 := by ring
        _ ≤ D ^ 8 * D ^ 8 := by
            have : 256 ≤ D ^ 8 := by
              calc 256 = 2 ^ 8 := by norm_num
                _ ≤ D ^ 8 := Nat.pow_le_pow_left hD2 8
            nlinarith
        _ = D ^ 16 := by ring
    omega
  have hD1 : 1 ≤ D := by omega
  have hDbig : 768 * K1 * 10000000 ≤ D ^ 4 := le_trans hDD0 (Nat.le_self_pow (by norm_num) D)
  have hdpos : (0 : ℝ) < d := by
    have : 1 ≤ d := le_trans hd01 hd
    exact_mod_cast this
  have hK1pos : (0 : ℝ) < K1 := by exact_mod_cast hK1
  set lam1 : ℝ := d / K1 with hlam1
  have hlam1pos : 0 < lam1 := by positivity
  -- the whole graph is a dense pair
  have hGS : DensePair G S lam1 := by
    refine ⟨hS, fun v hv => ?_, hsupp⟩
    have h1 : (d : ℝ) ≤ dS G S v := by exact_mod_cast hdeg v hv
    have h2 : lam1 ≤ d := by
      rw [hlam1, div_le_iff₀ hK1pos]
      have : (1 : ℝ) ≤ K1 := by exact_mod_cast hK1
      nlinarith
    linarith
  obtain ⟨F1, T1, hF1G, hD1', hmin1⟩ := realize G lam1 ⟨G, S, le_rfl, hGS⟩
  have hT1app := hT1 V G S d hS hc1 hdeg hsupp (LP F1) (fun F T hF hDT => hmin1 F T hF hDT)
  -- weight alternative gives (i)
  have hweight : (1 / 4 : ℝ) * Real.log D ≤ W G → 1 / 64 * Real.log d ≤ W G := by
    intro hw
    have : Real.log d ≤ 16 * Real.log D := by
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log hdpos
      have : ((D ^ 16 : ℕ) : ℝ) = (D : ℝ) ^ (16 : ℝ) := by
        rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; ring
      rw [← this]; exact_mod_cast hdD
    linarith
  rcases round G lam1 hlam1pos F1 T1 hF1G hD1' D hD1 with hw | ⟨h, hh, F', T', hF'G, hD', hLPF'⟩
  · left; exact hweight hw
  obtain ⟨F3, T3, hF3G, hD3, hmin3⟩ := realize G (lam1 / 128) ⟨F', T', hF'G, hD'⟩
  have hLP3 : LP F3 ≤ 6 * (h + 2) * D := le_trans (hmin3 F' T' hF'G hD') hLPF'
  have hLP3ge := LP_ge F3 T3 (lam1 / 128) (by positivity) hD3
  rcases round G (lam1 / 128) (by positivity) F3 T3 hF3G hD3 D hD1 with
    hw | ⟨h', hh', F'', T'', hF''G, hD'', hLPF''⟩
  · left; exact hweight hw
  obtain ⟨F6, T6, hF6, hD6, hT6⟩ := shrink F'' T'' (lam1 / 128 / 128) (by positivity) hD''
  right
  refine ⟨F6, le_trans hF6 hF''G, T6, hD6.1, fun v hv => ?_, ?_⟩
  · have h1 := hD6.2.1 v hv
    have h2 : ((d / (65536 * K1) : ℕ) : ℝ) ≤ (d : ℝ) / ((65536 * K1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : (d : ℝ) / ((65536 * K1 : ℕ) : ℝ) = lam1 / 128 / 128 / 4 := by
      rw [hlam1]; push_cast; field_simp; ring
    have : ((d / (65536 * K1) : ℕ) : ℝ) ≤ dS F6 T6 v := by linarith
    exact_mod_cast this
  · refine le_trans hT1app (wAbove_anti G ?_)
    have hdle : d ≤ 768 * K1 * ((h + 2) * D) := by
      have : (d : ℝ) / K1 / 128 ≤ ((6 * (h + 2) * D : ℕ) : ℝ) := by
        rw [← hlam1]; exact le_trans hLP3ge (by exact_mod_cast hLP3)
      rw [div_div, div_le_iff₀ (by positivity)] at this
      have : (d : ℝ) ≤ ((768 * K1 * ((h + 2) * D) : ℕ) : ℝ) := by push_cast at this ⊢; linarith
      exact_mod_cast this
    have hh'' : h' = 0 ∨ 5 ^ (h' - 1) ≤ 12 * (h + 2) * D + 2 := by
      rcases hh' with h0 | h0
      · left; exact h0
      · right
        have : 2 * LP F3 + 2 ≤ 12 * (h + 2) * D + 2 := by nlinarith
        omega
    have := arith K1 D h h' (LP F1) d hK1 hD1 hDbig hD8 hdle hh'' hh
    have : T6.card ≤ 12 * (h' + 2) * D + 2 := by nlinarith
    omega

end MLproof



section HTree

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- A binary tree in `G` with level growth `≥ 3/2` (a GKS ½-tree). Outside `VT` levels are `0`. -/
structure HTree where
  VT : Finset V
  lev : V → ℕ
  par : V → V
  h : ℕ
  root : V
  root_mem : root ∈ VT
  lev_root : lev root = 0
  root_uniq : ∀ v ∈ VT, lev v = 0 → v = root
  out : ∀ v, v ∉ VT → lev v = 0
  lev_le : ∀ v ∈ VT, lev v ≤ h
  par_mem : ∀ v ∈ VT, 1 ≤ lev v → par v ∈ VT
  par_adj : ∀ v ∈ VT, 1 ≤ lev v → G.Adj v (par v)
  par_lev : ∀ v ∈ VT, 1 ≤ lev v → lev (par v) = lev v - 1
  binary : ∀ v, (VT.filter (fun w => 1 ≤ lev w ∧ par w = v)).card ≤ 2
  growth : ∀ i < h, 3 * (VT.filter (fun v => lev v = i)).card ≤
    2 * (VT.filter (fun v => lev v = i + 1)).card

variable {G}

namespace HTree

variable (T : HTree G)

/-- level sets -/
def L (i : ℕ) : Finset V := T.VT.filter (fun v => T.lev v = i)

/-- children -/
def ch (v : V) : Finset V := T.VT.filter (fun w => 1 ≤ T.lev w ∧ T.par w = v)

lemma isParent : IsParent G T.par T.lev := by
  intro v hv
  have hvT : v ∈ T.VT := by
    by_contra h; rw [T.out v h] at hv; omega
  exact ⟨T.par_adj v hvT hv, T.par_lev v hvT hv⟩

lemma iter_mem (v : V) (hv : v ∈ T.VT) : ∀ t, t ≤ T.lev v → T.par^[t] v ∈ T.VT := by
  intro t
  induction t with
  | zero => intro _; simpa using hv
  | succ t ih =>
    intro ht
    rw [Function.iterate_succ_apply']
    apply T.par_mem _ (ih (by omega))
    rw [lev_iter T.isParent t v (by omega)]; omega

/-- ancestor at level `j` -/
def anc (j : ℕ) (v : V) : V := T.par^[T.lev v - j] v

lemma lev_anc (j : ℕ) (v : V) (hj : j ≤ T.lev v) : T.lev (T.anc j v) = j := by
  unfold anc; rw [lev_iter T.isParent _ v (by omega)]; omega

lemma anc_mem (j : ℕ) (v : V) (hv : v ∈ T.VT) : T.anc j v ∈ T.VT :=
  T.iter_mem v hv _ (by omega)

lemma anc_anc (j j' : ℕ) (v : V) (hjj : j' ≤ j) (hj : j ≤ T.lev v) :
    T.anc j' (T.anc j v) = T.anc j' v := by
  have h1 := T.lev_anc j v hj
  unfold anc at h1 ⊢
  rw [h1, ← Function.iterate_add_apply]; congr 1; omega

lemma anc_self (v : V) : T.anc (T.lev v) v = v := by simp [anc]

/-- `x, y` lie in a common cone of height `c` (rooted at level `h - c`). -/
def SC (c : ℕ) (x y : V) : Prop :=
  T.h - c ≤ T.lev x ∧ T.h - c ≤ T.lev y ∧ T.anc (T.h - c) x = T.anc (T.h - c) y

lemma SC.symm {c : ℕ} {x y : V} (h : T.SC c x y) : T.SC c y x := ⟨h.2.1, h.1, h.2.2.symm⟩

lemma SC.trans {c : ℕ} {x y z : V} (h1 : T.SC c x y) (h2 : T.SC c y z) : T.SC c x z :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

lemma SC.mono {c c' : ℕ} (hcc : c ≤ c') {x y : V} (h : T.SC c x y) : T.SC c' x y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  rw [← T.anc_anc (T.h - c) (T.h - c') x (by omega) h1, ← T.anc_anc (T.h - c) (T.h - c') y (by omega) h2,
    h3]

lemma SC_top (x y : V) (hx : x ∈ T.VT) (hy : y ∈ T.VT) : T.SC T.h x y := by
  refine ⟨by omega, by omega, ?_⟩
  simp only [Nat.sub_self]
  have h1 := T.anc_mem 0 x hx
  have h2 := T.anc_mem 0 y hy
  rw [T.root_uniq _ h1 (T.lev_anc 0 x (Nat.zero_le _)), T.root_uniq _ h2 (T.lev_anc 0 y (Nat.zero_le _))]

/-- descendants of `ρ` at level `lev ρ + k` -/
def desc (ρ : V) (k : ℕ) : Finset V :=
  T.VT.filter (fun v => T.lev v = T.lev ρ + k ∧ T.anc (T.lev ρ) v = ρ)

lemma desc_card (ρ : V) : ∀ k, (T.desc ρ k).card ≤ 2 ^ k := by
  intro k
  induction k with
  | zero =>
    have key : ∀ v ∈ T.desc ρ 0, v = ρ := by
      intro v hv
      simp only [desc, Finset.mem_filter, add_zero] at hv
      obtain ⟨_, h1, h2⟩ := hv
      unfold anc at h2; rw [h1, Nat.sub_self] at h2; simpa using h2
    simp only [pow_zero]
    exact Finset.card_le_one.mpr (fun a ha b hb => (key a ha).trans (key b hb).symm)
  | succ k ih =>
    have hsub : T.desc ρ (k + 1) ⊆ (T.desc ρ k).biUnion (fun u => T.ch u) := by
      intro v hv
      simp only [desc, Finset.mem_filter] at hv
      obtain ⟨hvT, hlv, hanc⟩ := hv
      rw [Finset.mem_biUnion]
      refine ⟨T.par v, ?_, ?_⟩
      · simp only [desc, Finset.mem_filter]
        refine ⟨T.par_mem v hvT (by omega), by rw [T.par_lev v hvT (by omega)]; omega, ?_⟩
        have : T.par v = T.anc (T.lev v - 1) v := by
          unfold anc; rw [show T.lev v - (T.lev v - 1) = 1 by omega]; rfl
        calc T.anc (T.lev ρ) (T.par v) = T.anc (T.lev ρ) (T.anc (T.lev v - 1) v) := by rw [this]
          _ = T.anc (T.lev ρ) v := T.anc_anc _ _ v (by omega) (by omega)
          _ = ρ := hanc
      · exact Finset.mem_filter.mpr ⟨hvT, by omega, rfl⟩
    calc (T.desc ρ (k + 1)).card ≤ ((T.desc ρ k).biUnion (fun u => T.ch u)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ T.desc ρ k, (T.ch u).card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ T.desc ρ k, 2 := Finset.sum_le_sum (fun u _ => T.binary u)
      _ = 2 * (T.desc ρ k).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- tops in a common cone of height `c` number at most `2^c` -/
lemma cone_card (c : ℕ) (hc : c ≤ T.h) (Q : Finset V) (hQ : ∀ x ∈ Q, x ∈ T.L T.h)
    (x0 : V) (hx0 : T.h - c ≤ T.lev x0) (hQc : ∀ x ∈ Q, T.SC c x0 x) : Q.card ≤ 2 ^ c := by
  set ρ := T.anc (T.h - c) x0
  have hρ : T.lev ρ = T.h - c := T.lev_anc _ x0 hx0
  refine le_trans (Finset.card_le_card ?_) (T.desc_card ρ c)
  intro x hx
  have h1 := hQ x hx
  simp only [L, Finset.mem_filter] at h1
  simp only [desc, Finset.mem_filter]
  refine ⟨h1.1, by omega, ?_⟩
  rw [hρ]; exact (hQc x hx).2.2.symm

end HTree

end HTree





section HTree2

variable {V : Type} [Fintype V] {G : SimpleGraph V}

namespace HTree

variable (T : HTree G)

lemma L_disj {i j : ℕ} (hij : i ≠ j) : Disjoint (T.L i) (T.L j) := by
  rw [Finset.disjoint_left]; intro v h1 h2
  simp only [L, Finset.mem_filter] at h1 h2; omega

lemma L_nonempty : ∀ i, i ≤ T.h → (T.L i).Nonempty := by
  intro i
  induction i with
  | zero => intro _; exact ⟨T.root, by simp [L, T.root_mem, T.lev_root]⟩
  | succ i ih =>
    intro hi
    have h1 := T.growth i (by omega)
    have h2 := (ih (by omega)).card_pos
    rw [← Finset.card_pos]; unfold L at h2 ⊢; omega

lemma sum_L_le : ∀ i, i ≤ T.h → ∑ j ∈ Finset.range (i + 1), (T.L j).card ≤ 3 * (T.L i).card := by
  intro i
  induction i with
  | zero => intro _; rw [Finset.sum_range_one]; omega
  | succ i ih =>
    intro hi
    rw [Finset.sum_range_succ]
    have := ih (by omega)
    have h2 := T.growth i (by omega)
    unfold L at *; omega

lemma VT_eq : T.VT = (Finset.range (T.h + 1)).biUnion T.L := by
  ext v; simp only [Finset.mem_biUnion, Finset.mem_range, L, Finset.mem_filter]
  constructor
  · intro hv; exact ⟨T.lev v, by have := T.lev_le v hv; omega, hv, rfl⟩
  · rintro ⟨_, _, hv, _⟩; exact hv

lemma VT_card : T.VT.card ≤ 3 * (T.L T.h).card := by
  rw [T.VT_eq]
  exact le_trans Finset.card_biUnion_le (T.sum_L_le T.h le_rfl)

lemma h_le_card : T.h ≤ Fintype.card V := by
  have h1 : ∑ j ∈ Finset.range (T.h + 1), (T.L j).card = T.VT.card := by
    rw [T.VT_eq, Finset.card_biUnion]
    intro i _ j _ hij; exact T.L_disj hij
  have h2 : ∑ j ∈ Finset.range (T.h + 1), 1 ≤ ∑ j ∈ Finset.range (T.h + 1), (T.L j).card :=
    Finset.sum_le_sum (fun j hj => (T.L_nonempty j (by simp at hj; omega)).card_pos)
  simp at h2
  have := Finset.card_le_univ T.VT
  omega

lemma L_pow (a : ℕ) (ha : a ≤ T.h) : 3 ^ a * (T.L (T.h - a)).card ≤ 2 ^ a * (T.L T.h).card := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := ih (by omega)
    have h2 := T.growth (T.h - (a + 1)) (by omega)
    rw [show T.h - (a + 1) + 1 = T.h - a by omega] at h2
    unfold L at *
    calc 3 ^ (a + 1) * (T.VT.filter (fun v => T.lev v = T.h - (a + 1))).card
        = 3 ^ a * (3 * (T.VT.filter (fun v => T.lev v = T.h - (a + 1))).card) := by ring
      _ ≤ 3 ^ a * (2 * (T.VT.filter (fun v => T.lev v = T.h - a)).card) :=
          Nat.mul_le_mul_left _ h2
      _ = 2 * (3 ^ a * (T.VT.filter (fun v => T.lev v = T.h - a)).card) := by ring
      _ ≤ 2 * (2 ^ a * (T.VT.filter (fun v => T.lev v = T.h)).card) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (a + 1) * (T.VT.filter (fun v => T.lev v = T.h)).card := by ring

/-- a valid partial extension of the top level: `A` gets two fresh private children each -/
def ValidExt (A : Finset V) (c : V → V × V) : Prop :=
  A ⊆ T.L T.h ∧ (∀ x ∈ A, G.Adj x (c x).1 ∧ G.Adj x (c x).2 ∧ (c x).1 ≠ (c x).2 ∧
    (c x).1 ∉ T.VT ∧ (c x).2 ∉ T.VT) ∧
  (∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → (c x).1 ≠ (c x').1 ∧ (c x).1 ≠ (c x').2 ∧ (c x).2 ≠ (c x').1 ∧
    (c x).2 ≠ (c x').2)

/-- new vertices of an extension -/
def Ys (A : Finset V) (c : V → V × V) : Finset V := A.image (fun x => (c x).1) ∪ A.image (fun x => (c x).2)

lemma Ys_card (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c) :
    (Ys A c).card = 2 * A.card := by
  unfold Ys
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn, Finset.card_image_of_injOn]
  · ring
  · intro x hx x' hx' e; by_contra hne; exact (hE.2.2 x hx x' hx' hne).2.2.2 e
  · intro x hx x' hx' e; by_contra hne; exact (hE.2.2 x hx x' hx' hne).1 e
  · rw [Finset.disjoint_left]; intro y h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨x', hx', e⟩ := h2
    by_cases hxx : x' = x
    · subst hxx; exact (hE.2.1 x' hx).2.2.1 e.symm
    · exact (hE.2.2 x' hx' x hx hxx).2.2.1 e

lemma Ys_disj (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c) : ∀ y ∈ Ys A c, y ∉ T.VT := by
  intro y hy
  simp only [Ys, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact (hE.2.1 x hx).2.2.2.1
  · exact (hE.2.1 x hx).2.2.2.2

end HTree

end HTree2



section HTree3

variable {V : Type} [Fintype V] {G : SimpleGraph V}

namespace HTree

/-- parent of a new vertex -/
def parY (A : Finset V) (c : V → V × V) (v : V) : V :=
  if h : ∃ x ∈ A, (c x).1 = v ∨ (c x).2 = v then Classical.choose h else v

lemma parY_spec (A : Finset V) (c : V → V × V) (v : V) (hv : v ∈ Ys A c) :
    parY A c v ∈ A ∧ ((c (parY A c v)).1 = v ∨ (c (parY A c v)).2 = v) := by
  have h : ∃ x ∈ A, (c x).1 = v ∨ (c x).2 = v := by
    simp only [Ys, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨x, hx, e⟩ | ⟨x, hx, e⟩
    · exact ⟨x, hx, Or.inl e⟩
    · exact ⟨x, hx, Or.inr e⟩
  simp only [parY, dif_pos h]
  exact Classical.choose_spec h

variable (T : HTree G)

lemma parY_uniq (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c) (v : V) (hv : v ∈ Ys A c)
    (x : V) (hx : x ∈ A) (hxv : (c x).1 = v ∨ (c x).2 = v) : parY A c v = x := by
  obtain ⟨h1, h2⟩ := parY_spec A c v hv
  by_contra hne
  have := hE.2.2 _ h1 x hx hne
  rcases h2 with e1 | e1 <;> rcases hxv with e2 | e2
  · exact this.1 (e1.trans e2.symm)
  · exact this.2.1 (e1.trans e2.symm)
  · exact this.2.2.1 (e1.trans e2.symm)
  · exact this.2.2.2 (e1.trans e2.symm)

lemma top_no_child (v : V) (hv : v ∈ T.L T.h) : T.ch v = ∅ := by
  ext w
  simp only [ch, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hw, h1, h2⟩
  have := T.par_lev w hw h1
  rw [h2] at this
  simp only [L, Finset.mem_filter] at hv
  have := T.lev_le w hw
  omega

/-- the extended tree -/
def ext (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c)
    (hbig : 3 * (T.L T.h).card ≤ 4 * A.card) : HTree G where
  VT := T.VT ∪ Ys A c
  lev v := if v ∈ Ys A c then T.h + 1 else T.lev v
  par v := if v ∈ Ys A c then parY A c v else T.par v
  h := T.h + 1
  root := T.root
  root_mem := Finset.mem_union_left _ T.root_mem
  lev_root := by
    have : T.root ∉ Ys A c := fun h => T.Ys_disj A c hE _ h T.root_mem
    simp [this, T.lev_root]
  root_uniq := by
    intro v hv h0
    by_cases hy : v ∈ Ys A c
    · simp [hy] at h0
    · simp only [hy, if_false] at h0
      rcases Finset.mem_union.mp hv with h | h
      · exact T.root_uniq v h h0
      · exact absurd h hy
  out := by
    intro v hv
    have h1 : v ∉ Ys A c := fun h => hv (Finset.mem_union_right _ h)
    have h2 : v ∉ T.VT := fun h => hv (Finset.mem_union_left _ h)
    simp [h1, T.out v h2]
  lev_le := by
    intro v hv
    by_cases hy : v ∈ Ys A c
    · simp [hy]
    · simp only [hy, if_false]
      rcases Finset.mem_union.mp hv with h | h
      · have := T.lev_le v h; omega
      · exact absurd h hy
  par_mem := by
    intro v hv h1
    by_cases hy : v ∈ Ys A c
    · simp only [hy, if_true]
      exact Finset.mem_union_left _ (Finset.mem_filter.mp (hE.1 (parY_spec A c v hy).1)).1
    · simp only [hy, if_false] at h1 ⊢
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_union_left _ (T.par_mem v h h1)
      · exact absurd h hy
  par_adj := by
    intro v hv h1
    by_cases hy : v ∈ Ys A c
    · simp only [hy, if_true]
      obtain ⟨hx, e⟩ := parY_spec A c v hy
      have := hE.2.1 _ hx
      rcases e with e | e
      · have h := this.1.symm; rw [e] at h; exact h
      · have h := this.2.1.symm; rw [e] at h; exact h
    · simp only [hy, if_false] at h1 ⊢
      rcases Finset.mem_union.mp hv with h | h
      · exact T.par_adj v h h1
      · exact absurd h hy
  par_lev := by
    intro v hv h1
    by_cases hy : v ∈ Ys A c
    · simp only [hy, if_true]
      obtain ⟨hx, _⟩ := parY_spec A c v hy
      have hxT := hE.1 hx
      simp only [L, Finset.mem_filter] at hxT
      have : parY A c v ∉ Ys A c := fun h => T.Ys_disj A c hE _ h hxT.1
      simp [this, hxT.2]
    · simp only [hy, if_false] at h1 ⊢
      rcases Finset.mem_union.mp hv with h | h
      · have hp := T.par_mem v h h1
        have : T.par v ∉ Ys A c := fun h' => T.Ys_disj A c hE _ h' hp
        simp [this, T.par_lev v h h1]
      · exact absurd h hy
  binary := by
    intro v
    by_cases hvA : v ∈ A
    · have hsub : (T.VT ∪ Ys A c).filter (fun w => 1 ≤ (if w ∈ Ys A c then T.h + 1 else T.lev w) ∧
          (if w ∈ Ys A c then parY A c w else T.par w) = v) ⊆ {(c v).1, (c v).2} := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_union] at hw
        obtain ⟨hw1, hw2, hw3⟩ := hw
        by_cases hy : w ∈ Ys A c
        · simp only [hy, if_true] at hw3
          obtain ⟨_, e⟩ := parY_spec A c w hy
          rw [hw3] at e
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases e with e | e
          · left; exact e.symm
          · right; exact e.symm
        · simp only [hy, if_false] at hw2 hw3
          rcases hw1 with hw1 | hw1
          · have hch : w ∈ T.ch v := Finset.mem_filter.mpr ⟨hw1, hw2, hw3⟩
            rw [T.top_no_child v (hE.1 hvA)] at hch
            simp at hch
          · exact absurd hw1 hy
      exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
    · have hsub : (T.VT ∪ Ys A c).filter (fun w => 1 ≤ (if w ∈ Ys A c then T.h + 1 else T.lev w) ∧
          (if w ∈ Ys A c then parY A c w else T.par w) = v) ⊆ T.ch v := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_union] at hw
        obtain ⟨hw1, hw2, hw3⟩ := hw
        by_cases hy : w ∈ Ys A c
        · simp only [hy, if_true] at hw3
          exact absurd (hw3 ▸ (parY_spec A c w hy).1) hvA
        · simp only [hy, if_false] at hw2 hw3
          rcases hw1 with hw1 | hw1
          · exact Finset.mem_filter.mpr ⟨hw1, hw2, hw3⟩
          · exact absurd hw1 hy
      exact le_trans (Finset.card_le_card hsub) (T.binary v)
  growth := by
    intro i hi
    have hL : ∀ j, j ≤ T.h → (T.VT ∪ Ys A c).filter
        (fun v => (if v ∈ Ys A c then T.h + 1 else T.lev v) = j) = T.L j := by
      intro j hj
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, L]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hy : v ∈ Ys A c
        · simp only [hy, if_true] at h2; omega
        · simp only [hy, if_false] at h2
          rcases h1 with h1 | h1
          · exact ⟨h1, h2⟩
          · exact absurd h1 hy
      · rintro ⟨h1, h2⟩
        have hy : v ∉ Ys A c := fun h => T.Ys_disj A c hE _ h h1
        exact ⟨Or.inl h1, by simp [hy, h2]⟩
    rcases Nat.lt_or_ge i T.h with hlt | hge
    · rw [hL i (by omega), hL (i + 1) (by omega)]; exact T.growth i hlt
    · have hi' : i = T.h := by omega
      subst hi'
      rw [hL T.h le_rfl]
      have hY : (T.VT ∪ Ys A c).filter
          (fun v => (if v ∈ Ys A c then T.h + 1 else T.lev v) = T.h + 1) = Ys A c := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          by_contra hy
          simp only [hy, if_false] at h2
          rcases h1 with h1 | h1
          · have := T.lev_le v h1; omega
          · exact hy h1
        · intro hy; exact ⟨Or.inr hy, by simp [hy]⟩
      rw [hY, T.Ys_card A c hE]
      omega

lemma ext_h (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c)
    (hbig : 3 * (T.L T.h).card ≤ 4 * A.card) : (T.ext A c hE hbig).h = T.h + 1 := rfl

end HTree

end HTree3




section HTree4

variable {V : Type} [Fintype V] {G : SimpleGraph V}

namespace HTree

/-- the one-vertex tree -/
def triv (r : V) : HTree G where
  VT := {r}
  lev _ := 0
  par v := v
  h := 0
  root := r
  root_mem := Finset.mem_singleton_self r
  lev_root := rfl
  root_uniq := fun v hv _ => Finset.mem_singleton.mp hv
  out := fun _ _ => rfl
  lev_le := fun _ _ => le_rfl
  par_mem := fun _ _ h => absurd h (by omega)
  par_adj := fun _ _ h => absurd h (by omega)
  par_lev := fun _ _ h => absurd h (by omega)
  binary := fun v => by simp
  growth := fun i hi => absurd hi (by omega)

/-- Maximal ½-tree with a maximal partial extension: the crown setup of GKS Lemma 2. -/
lemma exists_setup (r : V) : ∃ T : HTree G, T.root = r ∧ ∃ A : Finset V, ∃ c : V → V × V,
    T.ValidExt A c ∧ 4 * A.card < 3 * (T.L T.h).card ∧
    (∀ x ∈ T.L T.h, x ∉ A → ∀ w w', G.Adj x w → G.Adj x w' → w ∉ T.VT → w ∉ Ys A c →
      w' ∉ T.VT → w' ∉ Ys A c → w = w') := by
  let P : ℕ → Prop := fun k => ∃ T : HTree G, T.root = r ∧ T.h = k
  have hP0 : P 0 := ⟨triv r, rfl, rfl⟩
  obtain ⟨T, hTr, hTh⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le (Fintype.card V)) hP0
  have hmax : ∀ T' : HTree G, T'.root = r → T'.h ≤ T.h := by
    intro T' h1
    rw [hTh]
    exact Nat.le_findGreatest T'.h_le_card ⟨T', h1, rfl⟩
  refine ⟨T, hTr, ?_⟩
  have hne : ((Finset.univ : Finset (Finset V × (V → V × V))).filter
      (fun e => T.ValidExt e.1 e.2)).Nonempty :=
    ⟨(∅, fun v => (v, v)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.empty_subset _,
      fun x hx => absurd hx (Finset.notMem_empty x), fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩
  obtain ⟨⟨A, c⟩, hAc, hmaxA⟩ := Finset.exists_max_image _ (fun e => e.1.card) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hAc hmaxA
  refine ⟨A, c, hAc, ?_, ?_⟩
  · by_contra hbig
    push Not at hbig
    have := hmax (T.ext A c hAc hbig) hTr
    rw [ext_h] at this; omega
  · intro x hx hxA w w' hw hw' hwT hwY hw'T hw'Y
    by_contra hww
    set A' := insert x A
    set c' := Function.update c x (w, w')
    have hc'A : ∀ y ∈ A, c' y = c y := fun y hy =>
      Function.update_of_ne (fun e => hxA (by rw [← e]; exact hy)) _ _
    have hc'x : c' x = (w, w') := Function.update_self _ _ _
    have hYmem : ∀ y ∈ A, (c y).1 ∈ Ys A c ∧ (c y).2 ∈ Ys A c := fun y hy =>
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy),
        Finset.mem_union_right _ (Finset.mem_image_of_mem (fun x => (c x).2) hy)⟩
    have hvalid : T.ValidExt A' c' := by
      refine ⟨Finset.insert_subset hx hAc.1, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · rw [hc'x]; exact ⟨hw, hw', hww, hwT, hw'T⟩
        · rw [hc'A y hyA]; exact hAc.2.1 y hyA
      · intro y hy y' hy' hyy
        rcases Finset.mem_insert.mp hy with rfl | hyA <;> rcases Finset.mem_insert.mp hy' with rfl | hyA'
        · exact absurd rfl hyy
        · rw [hc'x, hc'A y' hyA']
          obtain ⟨h1, h2⟩ := hYmem y' hyA'
          exact ⟨fun e => hwY (by rw [show w = (c y').1 from e]; exact h1),
            fun e => hwY (by rw [show w = (c y').2 from e]; exact h2),
            fun e => hw'Y (by rw [show w' = (c y').1 from e]; exact h1),
            fun e => hw'Y (by rw [show w' = (c y').2 from e]; exact h2)⟩
        · rw [hc'x, hc'A y hyA]
          obtain ⟨h1, h2⟩ := hYmem y hyA
          exact ⟨fun e => hwY (by rw [show w = (c y).1 from e.symm]; exact h1),
            fun e => hw'Y (by rw [show w' = (c y).1 from e.symm]; exact h1),
            fun e => hwY (by rw [show w = (c y).2 from e.symm]; exact h2),
            fun e => hw'Y (by rw [show w' = (c y).2 from e.symm]; exact h2)⟩
        · rw [hc'A y hyA, hc'A y' hyA']; exact hAc.2.2 y hyA y' hyA' hyy
    have := hmaxA (A', c') hvalid
    simp only [A', Finset.card_insert_of_notMem hxA] at this
    omega

end HTree

end HTree4


section Crown

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G) (A : Finset V) (c : V → V × V)

namespace HTree

/-- the crown vertices `B`, new vertices `Y`, and `W = V(T) ∪ Y` -/
def Bc : Finset V := T.L T.h \ A
def Wc : Finset V := T.VT ∪ Ys A c

/-- the crown graph: non-tree edges from `B` into `W` -/
def CG : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ T.Bc A ∧ v ∈ T.Wc A c ∧ v ≠ T.par u) ∨
    (v ∈ T.Bc A ∧ u ∈ T.Wc A c ∧ u ≠ T.par v))
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.elim (fun h => Or.inr h) (fun h => Or.inl h)⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

lemma CG_adj (u v : V) : (T.CG A c).Adj u v ↔ G.Adj u v ∧ ((u ∈ T.Bc A ∧ v ∈ T.Wc A c ∧ v ≠ T.par u) ∨
    (v ∈ T.Bc A ∧ u ∈ T.Wc A c ∧ u ≠ T.par v)) := Iff.rfl

lemma CG_le : T.CG A c ≤ G := fun _ _ h => h.1

/-- a join from `x ∈ B` to a tree vertex `t` (direct, or through a new vertex) -/
def Join (x t : V) : Prop :=
  (T.CG A c).Adj x t ∨ ∃ y ∈ Ys A c, (T.CG A c).Adj x y ∧ (T.CG A c).Adj y t

lemma Bc_sub_VT : ∀ x ∈ T.Bc A, x ∈ T.VT := fun x hx =>
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1

lemma Bc_lev : ∀ x ∈ T.Bc A, T.lev x = T.h := fun x hx =>
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2

lemma CG_mem_W {u v : V} (h : (T.CG A c).Adj u v) : u ∈ T.Wc A c ∧ v ∈ T.Wc A c := by
  rcases h.2 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · exact ⟨Finset.mem_union_left _ (T.Bc_sub_VT A u h1), h2⟩
  · exact ⟨h2, Finset.mem_union_left _ (T.Bc_sub_VT A v h1)⟩

lemma SC_refl (k : ℕ) (x : V) (hx : T.h - k ≤ T.lev x) : T.SC k x x := ⟨hx, hx, rfl⟩

end HTree

end Crown


section Claim1

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G) (A : Finset V) (c : V → V × V)

namespace HTree

lemma VT_sub_S (S : Finset V) (hsupp : ∀ u v, G.Adj u v → v ∈ S) (hroot : T.root ∈ S) :
    ∀ v ∈ T.VT, v ∈ S := by
  intro v hv
  by_cases h0 : T.lev v = 0
  · rw [T.root_uniq v hv h0]; exact hroot
  · exact hsupp _ _ (T.par_adj v hv (by omega)).symm

lemma Bc_card (hA : 4 * A.card < 3 * (T.L T.h).card) (hAsub : A ⊆ T.L T.h) :
    4 * (T.Bc A).card > (T.L T.h).card ∧ (T.Wc A c).card ≤ 18 * (T.Bc A).card := by
  have h1 : (T.Bc A).card = (T.L T.h).card - A.card := by
    unfold Bc; rw [Finset.card_sdiff_of_subset hAsub]
  have h2 : (T.Wc A c).card ≤ T.VT.card + (Ys A c).card := Finset.card_union_le _ _
  have h3 : (Ys A c).card ≤ 2 * A.card := by
    unfold Ys
    exact le_trans (Finset.card_union_le _ _) (by
      have := Finset.card_image_le (s := A) (f := fun x => (c x).1)
      have := Finset.card_image_le (s := A) (f := fun x => (c x).2)
      omega)
  have h4 := T.VT_card
  have h5 : A.card ≤ (T.L T.h).card := Finset.card_le_card hAsub
  omega

lemma deg_B (S : Finset V) (d : ℕ) (hsupp : ∀ u v, G.Adj u v → v ∈ S) (hroot : T.root ∈ S)
    (hdeg : ∀ v ∈ S, d ≤ dS G S v)
    (hBprop : ∀ x ∈ T.L T.h, x ∉ A → ∀ w w', G.Adj x w → G.Adj x w' → w ∉ T.VT → w ∉ Ys A c →
      w' ∉ T.VT → w' ∉ Ys A c → w = w') :
    ∀ x ∈ T.Bc A, d ≤ dS (T.CG A c) (T.Wc A c) x + 2 := by
  intro x hx
  have hxS := T.VT_sub_S S hsupp hroot x (T.Bc_sub_VT A x hx)
  have hxtop := (Finset.mem_sdiff.mp hx).1
  have hxA := (Finset.mem_sdiff.mp hx).2
  have h1 := hdeg x hxS
  unfold dS at h1 ⊢
  have hsplit : S.filter (G.Adj x) ⊆ insert (T.par x) ((T.Wc A c).filter ((T.CG A c).Adj x)) ∪
      (S.filter (G.Adj x)).filter (fun w => w ∉ T.Wc A c) := by
    intro w hw
    by_cases hW : w ∈ T.Wc A c
    · apply Finset.mem_union_left
      by_cases hp : w = T.par x
      · rw [hp]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨hW, (Finset.mem_filter.mp hw).2, Or.inl ⟨hx, hW, hp⟩⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hW⟩)
  have hout : ((S.filter (G.Adj x)).filter (fun w => w ∉ T.Wc A c)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Wc, Finset.mem_union, not_or] at ha hb
    exact hBprop x hxtop hxA a b ha.1.2 hb.1.2 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  have := Finset.card_le_card hsplit
  have := Finset.card_union_le (insert (T.par x) ((T.Wc A c).filter ((T.CG A c).Adj x)))
    ((S.filter (G.Adj x)).filter (fun w => w ∉ T.Wc A c))
  have := Finset.card_insert_le (T.par x) ((T.Wc A c).filter ((T.CG A c).Adj x))
  omega

end HTree

end Claim1



section Claim1b

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G) (A : Finset V) (c : V → V × V)

namespace HTree

/-- edges of the crown with an endpoint in `A'` -/
def CA (A' : Finset V) : SimpleGraph V where
  Adj u v := (T.CG A c).Adj u v ∧ (u ∈ A' ∨ v ∈ A')
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1.1⟩

lemma SC_min {m : ℕ} {x y : V} (hx : x ∈ T.VT) (hy : y ∈ T.VT) (h : T.SC m x y) :
    T.SC (min m T.h) x y := by
  rcases le_total m T.h with hm | hm
  · rwa [min_eq_left hm]
  · rw [min_eq_right hm]; exact T.SC_top x y hx hy

/-- GKS Claim 1: at least half of `B` has a far join. -/
lemma claim1 (S : Finset V) (d : ℕ) (hsupp : ∀ u v, G.Adj u v → v ∈ S) (hroot : T.root ∈ S)
    (hdeg : ∀ v ∈ S, d ≤ dS G S v) (hd : 4 ≤ d) (hE : T.ValidExt A c)
    (hA : 4 * A.card < 3 * (T.L T.h).card)
    (hBprop : ∀ x ∈ T.L T.h, x ∉ A → ∀ w w', G.Adj x w → G.Adj x w' → w ∉ T.VT → w ∉ Ys A c →
      w' ∉ T.VT → w' ∉ Ys A c → w = w')
    (P : ℕ) (hP : ∀ F T', F ≤ G → DensePair F T' ((d : ℝ) / 144) → P ≤ LP F)
    (m : ℕ) (hm : 2 ^ (m + 2) ≤ P) :
    (T.Bc A).card ≤ 2 * ((T.Bc A).filter (fun x => ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t)).card := by
  by_contra hlt
  push Not at hlt
  set Far := (T.Bc A).filter (fun x => ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t)
  set A' := (T.Bc A).filter (fun x => ∀ t ∈ T.VT, T.Join A c x t → T.SC m x t) with hA'
  have hsplit : (T.Bc A).card = Far.card + A'.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x; simp only [Far, A', Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        by_cases h : ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t
        · left; exact ⟨hx, h⟩
        · right; push Not at h; exact ⟨hx, h⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Far, A', Finset.mem_filter] at h1 h2
      obtain ⟨t, ht, hj, hn⟩ := h1.2
      exact hn (h2.2 t ht hj)
  have hA'big : (T.Bc A).card < 2 * A'.card := by omega
  obtain ⟨hBc4, hWc⟩ := T.Bc_card A c hA hE.1
  have hA'B : ∀ x ∈ A', x ∈ T.Bc A := fun x hx => (Finset.mem_filter.mp hx).1
  set W := T.Wc A c
  set C := T.CA A c A'
  have hCdeg : ∀ x ∈ A', d ≤ dS C W x + 2 := by
    intro x hx
    have := T.deg_B A c S d hsupp hroot hdeg hBprop x (hA'B x hx)
    change d ≤ dS (T.CG A c) W x + 2 at this
    have e : dS C W x = dS (T.CG A c) W x := by
      unfold dS; congr 1; ext w
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, Or.inl hx⟩⟩
    omega
  have hA'W : ∀ x ∈ A', x ∈ W := fun x hx =>
    Finset.mem_union_left _ (T.Bc_sub_VT A x (hA'B x hx))
  have hk : (0 : ℝ) < ((d : ℝ) - 2) / 72 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_pos <;> linarith
  have hWne : W.Nonempty := by
    have : 0 < A'.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, hA'W x hx⟩
  have hsum : 2 * (((d : ℝ) - 2) / 72) * W.card ≤ ∑ u ∈ W, (dS C W u : ℝ) := by
    have h1 : ∑ u ∈ A', (dS C W u : ℝ) ≤ ∑ u ∈ W, (dS C W u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA'W (fun _ _ _ => by positivity)
    have h2 : (A'.card : ℝ) * ((d : ℝ) - 2) ≤ ∑ u ∈ A', (dS C W u : ℝ) := by
      have := Finset.card_nsmul_le_sum A' (fun u => (dS C W u : ℝ)) ((d : ℝ) - 2) (by
        intro x hx
        have := hCdeg x hx
        have : ((d : ℕ) : ℝ) ≤ (dS C W x : ℝ) + 2 := by exact_mod_cast this
        linarith)
      rwa [nsmul_eq_mul] at this
    have h3 : (W.card : ℝ) ≤ 36 * A'.card := by
      have : W.card ≤ 36 * A'.card := by omega
      exact_mod_cast this
    have h4 : (2 : ℝ) ≤ d := by
      have : (4 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    nlinarith
  obtain ⟨T2, hT2ne, hT2⟩ := exists_dense_subset C _ hk W hWne hsum
  set F := restr C T2
  have hFG : F ≤ G := fun u v h => (T.CG_le A c) ((restr_le C T2 h).1)
  have hDense : DensePair F T2 ((d : ℝ) / 144) := by
    refine ⟨hT2ne, fun v hv => ?_, restr_supported C T2⟩
    rw [dS_restr C T2 hv]
    have := hT2 v hv
    have : (d : ℝ) / 144 ≤ ((d : ℝ) - 2) / 72 := by
      have : (4 : ℝ) ≤ d := by exact_mod_cast hd
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
    linarith
  have hLP := hP F T2 hFG hDense
  obtain ⟨x0, _⟩ := hT2ne
  obtain ⟨u, v, p, hp, hpl⟩ := exists_LP F x0
  set ℓ := LP F
  let f : ℕ → V := fun i => p.getVert i
  have hCadj : ∀ i, i < ℓ → C.Adj (f i) (f (i + 1)) := fun i hi =>
    (restr_le C T2) (p.adj_getVert_succ (by omega))
  have hend : ∀ i, i < ℓ → f i ∈ A' ∨ f (i + 1) ∈ A' := fun i hi => (hCadj i hi).2
  have hfinj : ∀ i j, i ≤ ℓ → j ≤ ℓ → f i = f j → i = j := fun i j hi hj e =>
    hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) e
  have hA'VT : ∀ x ∈ A', x ∈ T.VT := fun x hx => T.Bc_sub_VT A x (hA'B x hx)
  have hA'lev : ∀ x ∈ A', T.lev x = T.h := fun x hx => T.Bc_lev A x (hA'B x hx)
  have hnear : ∀ x ∈ A', ∀ t ∈ T.VT, T.Join A c x t → T.SC m x t := fun x hx =>
    (Finset.mem_filter.mp hx).2
  have np : ∀ x ∈ A', ∀ x' ∈ A', C.Adj x x' → T.SC m x x' := fun x hx x' hx' h =>
    hnear x hx x' (hA'VT x' hx') (Or.inl h.1)
  have mid : ∀ x ∈ A', ∀ x' ∈ A', ∀ w, C.Adj x w → C.Adj w x' → T.SC m x x' := by
    intro x hx x' hx' w h1 h2
    have hwW := (T.CG_mem_W A c h1.1).2
    rcases Finset.mem_union.mp hwW with hwT | hwY
    · have s1 := hnear x hx w hwT (Or.inl h1.1)
      have s2 := hnear x' hx' w hwT (Or.inl h2.1.symm)
      exact SC.trans T s1 (SC.symm T s2)
    · exact hnear x hx x' (hA'VT x' hx') (Or.inr ⟨w, hwY, h1.1, h2.1⟩)
  have hℓ4 : 4 ≤ ℓ := by
    have : 4 ≤ 2 ^ (m + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set i0 := if f 0 ∈ A' then 0 else 1 with hi0
  have hi0A : f i0 ∈ A' := by
    by_cases h : f 0 ∈ A'
    · simp only [hi0, if_pos h]; exact h
    · simp only [hi0, if_neg h]
      rcases hend 0 (by omega) with h' | h'
      · exact absurd h' h
      · exact h'
  have hi01 : i0 ≤ 1 := by simp only [hi0]; split_ifs <;> omega
  have hall : ∀ j, j ≤ ℓ → f j ∈ A' → T.SC m (f i0) (f j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hjA
      by_cases hji : j ≤ i0
      · have : j = i0 := by
          by_contra hne
          have hj0 : j = 0 := by omega
          have hi1 : i0 = 1 := by omega
          rw [hj0] at hjA
          have : f 0 ∉ A' := by
            intro h; simp only [hi0, if_pos h] at hi1; omega
          exact this hjA
        rw [this]
        exact T.SC_refl m _ (by rw [hA'lev _ hi0A]; omega)
      · push Not at hji
        by_cases hprev : f (j - 1) ∈ A'
        · have e := hCadj (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at e
          exact SC.trans T (ih (j - 1) (by omega) (by omega) hprev) (np _ hprev _ hjA e)
        · have hj2 : 2 ≤ j := by
            by_contra h
            have : j = 1 := by omega
            subst this
            have hi00 : i0 = 0 := by omega
            have : f 0 ∈ A' := by
              by_contra h'; simp only [hi0, if_neg h'] at hi00; omega
            exact hprev this
          have hpp : f (j - 2) ∈ A' := by
            rcases hend (j - 2) (by omega) with h | h
            · exact h
            · rw [show j - 2 + 1 = j - 1 by omega] at h; exact absurd h hprev
          have e1 := hCadj (j - 2) (by omega)
          rw [show j - 2 + 1 = j - 1 by omega] at e1
          have e2 := hCadj (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at e2
          have hge : i0 ≤ j - 2 := by
            by_contra h
            have hi1 : i0 = 1 := by omega
            have hj2' : j - 2 = 0 := by omega
            rw [hj2'] at hpp
            have : i0 = 0 := by simp only [hi0, if_pos hpp]
            omega
          by_cases heq : j - 2 = i0
          · rw [← heq]; exact mid _ hpp _ hjA _ e1 e2
          · exact SC.trans T (ih (j - 2) (by omega) (by omega) hpp) (mid _ hpp _ hjA _ e1 e2)
  -- counting
  let g : ℕ → V := fun k => if f (2 * k) ∈ A' then f (2 * k) else f (2 * k + 1)
  set Q := (Finset.range (ℓ / 2)).image g
  have hgA : ∀ k, k < ℓ / 2 → g k ∈ A' ∧ (g k = f (2 * k) ∨ g k = f (2 * k + 1)) := by
    intro k hk
    simp only [g]
    split_ifs with h
    · exact ⟨h, Or.inl rfl⟩
    · rcases hend (2 * k) (by omega) with h' | h'
      · exact absurd h' h
      · exact ⟨h', Or.inr rfl⟩
  have hQcard : Q.card = ℓ / 2 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk k' hk' e
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    obtain ⟨_, hk1⟩ := hgA k hk
    obtain ⟨_, hk2⟩ := hgA k' hk'
    rcases hk1 with e1 | e1 <;> rcases hk2 with e2 | e2 <;> rw [e1, e2] at e <;>
      have := hfinj _ _ (by omega) (by omega) e <;> omega
  have hQ1 : ∀ x ∈ Q, x ∈ T.L T.h := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_sdiff.mp (hA'B _ (hgA k (Finset.mem_range.mp hk)).1)).1
  have hQ2 : ∀ x ∈ Q, T.SC (min m T.h) (f i0) x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hk' := Finset.mem_range.mp hk
    obtain ⟨hA'k, hpos⟩ := hgA k hk'
    have hpos' : ∃ j, j ≤ ℓ ∧ g k = f j := by
      rcases hpos with e | e
      · exact ⟨2 * k, by omega, e⟩
      · exact ⟨2 * k + 1, by omega, e⟩
    obtain ⟨j, hj, e⟩ := hpos'
    have := hall j hj (e ▸ hA'k)
    rw [← e] at this
    exact T.SC_min (hA'VT _ hi0A) (hA'VT _ hA'k) this
  have hcc := T.cone_card (min m T.h) (min_le_right _ _) Q hQ1 (f i0)
    (by rw [hA'lev _ hi0A]; omega) hQ2
  rw [hQcard] at hcc
  have : 2 ^ (min m T.h) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
  omega

end HTree

end Claim1b




section Claim2

lemma sum_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) :
    ∑ n ∈ Finset.Icc a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have key : ∀ b, ∑ n ∈ Finset.Icc a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) - 1 / (max b (a - 1) : ℕ) := by
    intro b
    induction b with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp only [Finset.sum_empty]
      have : max 0 (a - 1) = a - 1 := by omega
      rw [this]
      have h1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [h1]; simp
    | succ b ih =>
      by_cases hb : b + 1 < a
      · rw [Finset.Icc_eq_empty (by omega)]
        simp only [Finset.sum_empty]
        have : max (b + 1) (a - 1) = a - 1 := by omega
        rw [this]
        have h1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [h1]; simp
      · rw [Finset.sum_Icc_succ_top (by omega)]
        have hm1 : max (b + 1) (a - 1) = b + 1 := by omega
        have hm2 : max b (a - 1) = b := by omega
        rw [hm2] at ih; rw [hm1]
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
        have : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  have := key b
  have : (0 : ℝ) ≤ 1 / (max b (a - 1) : ℕ) := by positivity
  linarith

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G) (A : Finset V) (c : V → V × V)

namespace HTree

/-- vertices of `B` with a join at cone distance exactly `n` to a vertex at level `k` -/
def Zs (n k : ℕ) : Finset V :=
  (T.Bc A).filter (fun x => ∃ t ∈ T.VT, T.Join A c x t ∧ T.SC n x t ∧ ¬ T.SC (n - 1) x t ∧ T.lev t = k)

/-- GKS Claim 2: a scale `n > m` and a level `k` carrying many exact `n`-joins. -/
lemma claim2 (m : ℕ) (hm : 1 ≤ m) (Far : Finset V)
    (hFar : ∀ x ∈ Far, x ∈ T.Bc A ∧ ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t) (hne : Far.Nonempty) :
    ∃ n k, m < n ∧ n ≤ T.h ∧ T.h - n ≤ k ∧ k ≤ T.h ∧
      Far.card ≤ 2 * n ^ 2 * (n + 1) * (T.Zs A c n k).card := by
  -- the n-sets
  let X : ℕ → Finset V := fun n => (T.Bc A).filter
    (fun x => ∃ t ∈ T.VT, T.Join A c x t ∧ T.SC n x t ∧ ¬ T.SC (n - 1) x t)
  have hcover : Far ⊆ (Finset.Icc (m + 1) T.h).biUnion X := by
    intro x hx
    obtain ⟨hxB, t, ht, hj, hnf⟩ := hFar x hx
    have hex : ∃ n, T.SC n x t := ⟨T.h, T.SC_top x t (T.Bc_sub_VT A x hxB) ht⟩
    set n := Nat.find hex
    have hn := Nat.find_spec hex
    have hnh : n ≤ T.h := Nat.find_min' hex (T.SC_top x t (T.Bc_sub_VT A x hxB) ht)
    have hnm : m < n := by
      by_contra h; push Not at h
      exact hnf (SC.mono T h hn)
    rw [Finset.mem_biUnion]
    refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, hnh⟩, Finset.mem_filter.mpr ⟨hxB, t, ht, hj, hn, ?_⟩⟩
    exact Nat.find_min hex (show n - 1 < n by omega)
  have hsum : (Far.card : ℝ) ≤ ∑ n ∈ Finset.Icc (m + 1) T.h, ((X n).card : ℝ) := by
    have := le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    exact_mod_cast this
  have hn_exists : ∃ n ∈ Finset.Icc (m + 1) T.h, (Far.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 * (X n).card := by
    by_contra hcon
    push Not at hcon
    have hFpos : (0 : ℝ) < Far.card := by exact_mod_cast hne.card_pos
    have h1 : ∑ n ∈ Finset.Icc (m + 1) T.h, ((X n).card : ℝ) ≤
        ∑ n ∈ Finset.Icc (m + 1) T.h, (Far.card : ℝ) * (1 / (2 * (n : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by
        have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 1 ≤ n by omega)
      have := (hcon n hn).le
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ n ∈ Finset.Icc (m + 1) T.h, (1 : ℝ) / (2 * (n : ℝ) ^ 2) ≤ 1 / 2 := by
      have := sum_inv_sq_le (m + 1) T.h (by omega)
      have e : ∑ n ∈ Finset.Icc (m + 1) T.h, (1 : ℝ) / (2 * (n : ℝ) ^ 2) =
          (1 / 2) * ∑ n ∈ Finset.Icc (m + 1) T.h, (1 : ℝ) / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; field_simp
      rw [e]
      have hm' : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) - 1 := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        push_cast; linarith
      have : 1 / (((m + 1 : ℕ) : ℝ) - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hm'
      nlinarith
    nlinarith
  obtain ⟨n, hn, hFn⟩ := hn_exists
  have hnI := Finset.mem_Icc.mp hn
  -- level pigeonhole
  have hcover2 : X n ⊆ (Finset.Icc (T.h - n) T.h).biUnion (fun k => T.Zs A c n k) := by
    intro x hx
    obtain ⟨hxB, t, ht, hj, hsc, hnsc⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_biUnion]
    exact ⟨T.lev t, Finset.mem_Icc.mpr ⟨hsc.2.1, T.lev_le t ht⟩,
      Finset.mem_filter.mpr ⟨hxB, t, ht, hj, hsc, hnsc, rfl⟩⟩
  have hk_exists : ∃ k ∈ Finset.Icc (T.h - n) T.h, (X n).card ≤ (n + 1) * (T.Zs A c n k).card := by
    by_contra hcon
    push Not at hcon
    have h1 := le_trans (Finset.card_le_card hcover2) Finset.card_biUnion_le
    have hne2 : (Finset.Icc (T.h - n) T.h).Nonempty := ⟨T.h, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
    have h2 : ∑ k ∈ Finset.Icc (T.h - n) T.h, (n + 1) * (T.Zs A c n k).card <
        ∑ k ∈ Finset.Icc (T.h - n) T.h, (X n).card := Finset.sum_lt_sum_of_nonempty hne2 hcon
    rw [← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h2
    have : T.h + 1 - (T.h - n) = n + 1 := by omega
    rw [this] at h2
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  obtain ⟨k, hk, hXk⟩ := hk_exists
  have hkI := Finset.mem_Icc.mp hk
  refine ⟨n, k, by omega, hnI.2, hkI.1, hkI.2, ?_⟩
  have : (Far.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 * ((n + 1) * (T.Zs A c n k).card : ℕ) := by
    refine le_trans hFn ?_
    gcongr
  have : Far.card ≤ 2 * n ^ 2 * ((n + 1) * (T.Zs A c n k).card) := by exact_mod_cast this
  calc Far.card ≤ 2 * n ^ 2 * ((n + 1) * (T.Zs A c n k).card) := this
    _ = 2 * n ^ 2 * (n + 1) * (T.Zs A c n k).card := by ring

end HTree

end Claim2



section Claim34

lemma num1_aux : ∀ j, 18 ≤ j → 32 ^ (j + 1) * ((4 * j + 4) ^ 2 * (4 * j + 5)) ≤ 81 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 32 * ((4 * (j + 1) + 4) ^ 2 * (4 * (j + 1) + 5)) ≤ 81 * ((4 * j + 4) ^ 2 * (4 * j + 5)) := by
      nlinarith
    calc 32 ^ (j + 1 + 1) * ((4 * (j + 1) + 4) ^ 2 * (4 * (j + 1) + 5))
        = 32 ^ (j + 1) * (32 * ((4 * (j + 1) + 4) ^ 2 * (4 * (j + 1) + 5))) := by ring
      _ ≤ 32 ^ (j + 1) * (81 * ((4 * j + 4) ^ 2 * (4 * j + 5))) := Nat.mul_le_mul_left _ h1
      _ = 81 * (32 ^ (j + 1) * ((4 * j + 4) ^ 2 * (4 * j + 5))) := by ring
      _ ≤ 81 * 81 ^ j := Nat.mul_le_mul_left _ ih
      _ = 81 ^ (j + 1) := by ring

/-- small cones carry few tops -/
lemma num1 (n : ℕ) (hn : 73 ≤ n) : 32 * n ^ 2 * (n + 1) * 2 ^ ((n - 1) / 4) * 2 ^ (n - 1) ≤ 3 ^ (n - 1) := by
  set j := (n - 1) / 4
  set r := (n - 1) % 4
  have hnr : n - 1 = 4 * j + r := (Nat.div_add_mod (n - 1) 4).symm
  have hr : r < 4 := Nat.mod_lt _ (by norm_num)
  have hj : 18 ≤ j := by omega
  have h1 := num1_aux j hj
  have e2 : 2 ^ j * 2 ^ (n - 1) = 32 ^ j * 2 ^ r := by
    rw [hnr, pow_add, pow_mul, show (32 : ℕ) = 2 * 2 ^ 4 by norm_num, mul_pow]; ring
  have e3 : 3 ^ (n - 1) = 81 ^ j * 3 ^ r := by rw [hnr, pow_add, pow_mul]; ring
  have h23 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by norm_num) r
  have hn' : n ≤ 4 * j + 4 := by omega
  have h4 : 32 * n ^ 2 * (n + 1) ≤ 32 * ((4 * j + 4) ^ 2 * (4 * j + 5)) := by
    have : n ^ 2 ≤ (4 * j + 4) ^ 2 := Nat.pow_le_pow_left hn' 2
    have : n + 1 ≤ 4 * j + 5 := by omega
    nlinarith
  calc 32 * n ^ 2 * (n + 1) * 2 ^ j * 2 ^ (n - 1)
      = (32 * n ^ 2 * (n + 1)) * (2 ^ j * 2 ^ (n - 1)) := by ring
    _ = (32 * n ^ 2 * (n + 1)) * (32 ^ j * 2 ^ r) := by rw [e2]
    _ ≤ (32 * ((4 * j + 4) ^ 2 * (4 * j + 5))) * (32 ^ j * 3 ^ r) := by gcongr
    _ = (32 ^ (j + 1) * ((4 * j + 4) ^ 2 * (4 * j + 5))) * 3 ^ r := by ring
    _ ≤ 81 ^ j * 3 ^ r := Nat.mul_le_mul_right _ h1
    _ = 3 ^ (n - 1) := e3.symm

lemma num2_aux : ∀ j, 31 ≤ j → 64 * ((8 * j + 8) ^ 2 * (8 * j + 9)) < 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 64 * ((8 * (j + 1) + 8) ^ 2 * (8 * (j + 1) + 9)) ≤ 2 * (64 * ((8 * j + 8) ^ 2 * (8 * j + 9))) := by
      nlinarith
    calc 64 * ((8 * (j + 1) + 8) ^ 2 * (8 * (j + 1) + 9)) ≤ 2 * (64 * ((8 * j + 8) ^ 2 * (8 * j + 9))) := h1
      _ < 2 * 2 ^ j := by omega
      _ = 2 ^ (j + 1) := by ring

/-- many branchings: `2^((n-1)/4) ≤ 2^t * 32 n²(n+1)` forces `n/8 ≤ t` -/
lemma num2 (n t : ℕ) (hn : 248 ≤ n) (h : 2 ^ ((n - 1) / 4) ≤ 2 ^ t * (32 * n ^ 2 * (n + 1))) :
    n / 8 ≤ t := by
  by_contra hlt
  push Not at hlt
  set j := n / 8
  have hj : 31 ≤ j := by omega
  have h1 := num2_aux j hj
  have hu : 2 * j - 1 ≤ (n - 1) / 4 := by omega
  have hn8 : n ≤ 8 * j + 8 := by omega
  have h2 : 2 ^ t ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 32 * n ^ 2 * (n + 1) ≤ 32 * ((8 * j + 8) ^ 2 * (8 * j + 9)) := by
    have : n ^ 2 ≤ (8 * j + 8) ^ 2 := Nat.pow_le_pow_left hn8 2
    have : n + 1 ≤ 8 * j + 9 := by omega
    nlinarith
  have h4 : 2 ^ (2 * j - 1) ≤ 2 ^ ((n - 1) / 4) := Nat.pow_le_pow_right (by norm_num) hu
  have e : 2 ^ (2 * j - 1) = 2 ^ (j - 1) * 2 ^ j := by rw [← pow_add]; congr 1; omega
  have : 2 ^ (j - 1) * 2 ^ j ≤ 2 ^ (j - 1) * (32 * ((8 * j + 8) ^ 2 * (8 * j + 9))) := by
    calc 2 ^ (j - 1) * 2 ^ j = 2 ^ (2 * j - 1) := e.symm
      _ ≤ 2 ^ ((n - 1) / 4) := h4
      _ ≤ 2 ^ t * (32 * n ^ 2 * (n + 1)) := h
      _ ≤ 2 ^ (j - 1) * (32 * ((8 * j + 8) ^ 2 * (8 * j + 9))) := Nat.mul_le_mul h2 h3
  have := Nat.le_of_mul_le_mul_left this (by positivity)
  omega

end Claim34



section Claim34b

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G)

namespace HTree

lemma anc_of_ch {v w : V} (hw : w ∈ T.ch v) : T.lev w = T.lev v + 1 ∧ T.anc (T.lev v) w = v := by
  obtain ⟨hwT, h1, h2⟩ := Finset.mem_filter.mp hw
  have hl := T.par_lev w hwT h1
  rw [h2] at hl
  refine ⟨by omega, ?_⟩
  unfold anc; rw [show T.lev w - T.lev v = 1 by omega]; simpa using h2

lemma ch_mem {v w : V} (hw : w ∈ T.ch v) : w ∈ T.VT := (Finset.mem_filter.mp hw).1

lemma desc_split (v : V) (hv : v ∈ T.VT) (hlt : T.lev v < T.h) :
    T.desc v (T.h - T.lev v) = (T.ch v).biUnion (fun w => T.desc w (T.h - T.lev w)) := by
  ext x
  simp only [desc, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hl, ha⟩
    set w := T.anc (T.lev v + 1) x
    have hlw : T.lev w = T.lev v + 1 := T.lev_anc _ x (by omega)
    have hwT : w ∈ T.VT := T.anc_mem _ x hx
    refine ⟨w, ?_, hx, by omega, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hwT, by omega, ?_⟩
      have : T.par w = T.anc (T.lev v) w := by
        unfold anc; rw [hlw, show T.lev v + 1 - T.lev v = 1 by omega]; rfl
      rw [this, T.anc_anc _ _ x (by omega) (by omega), ha]
    · rw [hlw]
  · rintro ⟨w, hw, hx, hl, ha⟩
    obtain ⟨hlw, haw⟩ := T.anc_of_ch hw
    refine ⟨hx, by omega, ?_⟩
    calc T.anc (T.lev v) x = T.anc (T.lev v) (T.anc (T.lev w) x) :=
          (T.anc_anc _ _ x (by omega) (by omega)).symm
      _ = T.anc (T.lev v) w := by rw [ha]
      _ = v := haw

lemma desc_disj (v w w' : V) (hw : w ∈ T.ch v) (hw' : w' ∈ T.ch v) (hne : w ≠ w') :
    Disjoint (T.desc w (T.h - T.lev w)) (T.desc w' (T.h - T.lev w')) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  simp only [desc, Finset.mem_filter] at h1 h2
  obtain ⟨hlw, _⟩ := T.anc_of_ch hw
  obtain ⟨hlw', _⟩ := T.anc_of_ch hw'
  apply hne
  rw [← h1.2.2, ← h2.2.2, hlw, hlw']

variable (Z : Finset V)

/-- number of `Z`-tops below `v` -/
def Zc (v : V) : ℕ := ((T.desc v (T.h - T.lev v)).filter (· ∈ Z)).card

lemma Zc_split (v : V) (hv : v ∈ T.VT) (hlt : T.lev v < T.h) :
    T.Zc Z v = ∑ w ∈ T.ch v, T.Zc Z w := by
  unfold Zc
  rw [T.desc_split v hv hlt, Finset.filter_biUnion, Finset.card_biUnion]
  intro w hw w' hw' hne
  exact Finset.disjoint_filter_filter (T.desc_disj v w w' hw hw' hne)

/-- heavy child -/
def heavy (v : V) : V :=
  if h : (T.ch v).Nonempty then Classical.choose (Finset.exists_max_image (T.ch v) (T.Zc Z) h) else v

lemma heavy_spec (v : V) (h : (T.ch v).Nonempty) :
    T.heavy Z v ∈ T.ch v ∧ ∀ w ∈ T.ch v, T.Zc Z w ≤ T.Zc Z (T.heavy Z v) := by
  simp only [heavy, dif_pos h]
  exact Classical.choose_spec (Finset.exists_max_image (T.ch v) (T.Zc Z) h)

/-- branching: a second child carries `Z`-tops -/
def Br (v : V) : Prop := ∃ w ∈ T.ch v, w ≠ T.heavy Z v ∧ 0 < T.Zc Z w

lemma heavy_step (v : V) (hv : v ∈ T.VT) (hlt : T.lev v < T.h) (hpos : 0 < T.Zc Z v) :
    T.heavy Z v ∈ T.ch v ∧ T.Zc Z v ≤ 2 * T.Zc Z (T.heavy Z v) ∧
      (¬ T.Br Z v → T.Zc Z v ≤ T.Zc Z (T.heavy Z v)) := by
  have hsplit := T.Zc_split Z v hv hlt
  have hne : (T.ch v).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsplit; omega
  obtain ⟨hmem, hmax⟩ := T.heavy_spec Z v hne
  refine ⟨hmem, ?_, ?_⟩
  · rw [hsplit]
    calc ∑ w ∈ T.ch v, T.Zc Z w ≤ ∑ w ∈ T.ch v, T.Zc Z (T.heavy Z v) := Finset.sum_le_sum hmax
      _ = (T.ch v).card * T.Zc Z (T.heavy Z v) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 * T.Zc Z (T.heavy Z v) := Nat.mul_le_mul_right _ (T.binary v)
  · intro hnb
    rw [hsplit, ← Finset.add_sum_erase _ _ hmem]
    have : ∑ w ∈ (T.ch v).erase (T.heavy Z v), T.Zc Z w = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      by_contra hpos'
      exact hnb ⟨w, Finset.mem_of_mem_erase hw, Finset.ne_of_mem_erase hw, Nat.pos_of_ne_zero hpos'⟩
    omega

end HTree

end Claim34b



section Claim34c

variable {V : Type} [Fintype V] {G : SimpleGraph V} (T : HTree G) (Z : Finset V)

namespace HTree

/-- the heavy path from `ρ` -/
def hp (ρ : V) (i : ℕ) : V := (T.heavy Z)^[i] ρ

lemma heavy_path (ρ : V) (hρ : ρ ∈ T.VT) (hpos : 0 < T.Zc Z ρ) :
    ∀ i, i ≤ T.h - T.lev ρ → T.hp Z ρ i ∈ T.VT ∧ T.lev (T.hp Z ρ i) = T.lev ρ + i ∧
      0 < T.Zc Z (T.hp Z ρ i) ∧
      T.Zc Z ρ ≤ 2 ^ ((Finset.range i).filter (fun j => T.Br Z (T.hp Z ρ j))).card * T.Zc Z (T.hp Z ρ i) ∧
      (∀ j, j ≤ i → T.anc (T.lev ρ + j) (T.hp Z ρ i) = T.hp Z ρ j) := by
  intro i
  induction i with
  | zero =>
    intro _
    have e0 : T.hp Z ρ 0 = ρ := rfl
    refine ⟨by rw [e0]; exact hρ, by rw [e0]; omega, by rw [e0]; exact hpos, by simp [e0], fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this; rw [e0, add_zero, T.anc_self]
  | succ i ih =>
    intro hi
    obtain ⟨hT, hl, hz, hc, ha⟩ := ih (by omega)
    have hlt : T.lev (T.hp Z ρ i) < T.h := by omega
    obtain ⟨hmem, h2, h3⟩ := T.heavy_step Z _ hT hlt hz
    have hnext : T.hp Z ρ (i + 1) = T.heavy Z (T.hp Z ρ i) := by
      simp only [hp]; rw [Function.iterate_succ_apply']
    rw [hnext]
    obtain ⟨hlw, haw⟩ := T.anc_of_ch hmem
    refine ⟨T.ch_mem hmem, by omega, by omega, ?_, ?_⟩
    · rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hb : T.Br Z (T.hp Z ρ i)
      · rw [if_pos hb, Finset.card_insert_of_notMem (by simp), pow_succ]
        calc T.Zc Z ρ ≤ 2 ^ _ * T.Zc Z (T.hp Z ρ i) := hc
          _ ≤ 2 ^ _ * (2 * T.Zc Z (T.heavy Z (T.hp Z ρ i))) := Nat.mul_le_mul_left _ h2
          _ = _ := by ring
      · rw [if_neg hb]
        exact le_trans hc (Nat.mul_le_mul_left _ (h3 hb))
    · intro j hj
      rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
      · calc T.anc (T.lev ρ + j) (T.heavy Z (T.hp Z ρ i))
            = T.anc (T.lev ρ + j) (T.anc (T.lev (T.hp Z ρ i)) (T.heavy Z (T.hp Z ρ i))) :=
              (T.anc_anc _ _ _ (by omega) (by omega)).symm
          _ = T.anc (T.lev ρ + j) (T.hp Z ρ i) := by rw [haw]
          _ = T.hp Z ρ j := ha j (by omega)
      · have : j = i + 1 := by omega
        subst this
        rw [hnext, show T.lev ρ + (i + 1) = T.lev (T.heavy Z (T.hp Z ρ i)) by omega, T.anc_self]

lemma Zc_top (v : V) (hv : T.lev v = T.h) (hvT : v ∈ T.VT) (hpos : 0 < T.Zc Z v) : v ∈ Z := by
  unfold Zc at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [desc, Finset.mem_filter, hv, Nat.sub_self, add_zero] at hx
  have : x = v := by
    obtain ⟨⟨_, h1, h2⟩, _⟩ := hx
    unfold anc at h2; rw [h1, Nat.sub_self] at h2; simpa using h2
  rw [← this]; exact hx.2

/-- GKS Claim 3: a large cone of height `n-1` rich in `Z`. -/
lemma claim3 (n : ℕ) (hn : 73 ≤ n) (hnh : n ≤ T.h) (hZ : Z ⊆ T.L T.h)
    (hbig : (T.L T.h).card < 16 * n ^ 2 * (n + 1) * Z.card) :
    ∃ ρ ∈ T.L (T.h - n + 1), 2 ^ ((n - 1) / 4) ≤ (T.desc ρ (n - 1)).card ∧
      (T.desc ρ (n - 1)).card ≤ 32 * n ^ 2 * (n + 1) * ((T.desc ρ (n - 1)).filter (· ∈ Z)).card := by
  set q := T.h - n + 1
  set K := 32 * n ^ 2 * (n + 1)
  set θ := 2 ^ ((n - 1) / 4)
  have hpart : T.L T.h = (T.L q).biUnion (fun ρ => T.desc ρ (n - 1)) := by
    ext x
    simp only [Finset.mem_biUnion, L, desc, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hl⟩
      refine ⟨T.anc q x, ⟨T.anc_mem q x hx, T.lev_anc q x (by omega)⟩, hx, ?_, ?_⟩
      · rw [T.lev_anc q x (by omega)]; omega
      · rw [T.lev_anc q x (by omega)]
    · rintro ⟨ρ, ⟨_, hρ⟩, hx, hl, _⟩
      exact ⟨hx, by omega⟩
  have hdisj : ∀ ρ ∈ T.L q, ∀ ρ' ∈ T.L q, ρ ≠ ρ' → Disjoint (T.desc ρ (n - 1)) (T.desc ρ' (n - 1)) := by
    intro ρ hρ ρ' hρ' hne
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [desc, Finset.mem_filter, L] at h1 h2 hρ hρ'
    apply hne; rw [← h1.2.2, ← h2.2.2, hρ.2, hρ'.2]
  by_contra hcon
  push Not at hcon
  have hZsum : Z.card = ∑ ρ ∈ T.L q, ((T.desc ρ (n - 1)).filter (· ∈ Z)).card := by
    rw [← Finset.card_biUnion (fun ρ hρ ρ' hρ' hne => Finset.disjoint_filter_filter (hdisj ρ hρ ρ' hρ' hne)),
      ← Finset.filter_biUnion, ← hpart]
    congr 1; ext x; simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hZ h, h⟩, fun h => h.2⟩
  have htop : (T.L T.h).card = ∑ ρ ∈ T.L q, (T.desc ρ (n - 1)).card := by
    rw [hpart, Finset.card_biUnion hdisj]
  have hper : ∀ ρ ∈ T.L q, K * ((T.desc ρ (n - 1)).filter (· ∈ Z)).card ≤ K * θ + (T.desc ρ (n - 1)).card := by
    intro ρ hρ
    have hsub := Finset.card_filter_le (T.desc ρ (n - 1)) (· ∈ Z)
    by_cases hs : θ ≤ (T.desc ρ (n - 1)).card
    · have := hcon ρ hρ hs; omega
    · push Not at hs
      have : K * ((T.desc ρ (n - 1)).filter (· ∈ Z)).card ≤ K * θ := Nat.mul_le_mul_left _ (by omega)
      omega
  have hsum : K * Z.card ≤ K * θ * (T.L q).card + (T.L T.h).card := by
    rw [hZsum, Finset.mul_sum, htop]
    calc ∑ ρ ∈ T.L q, K * ((T.desc ρ (n - 1)).filter (· ∈ Z)).card
        ≤ ∑ ρ ∈ T.L q, (K * θ + (T.desc ρ (n - 1)).card) := Finset.sum_le_sum hper
      _ = K * θ * (T.L q).card + ∑ ρ ∈ T.L q, (T.desc ρ (n - 1)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
  have hLq : 3 ^ (n - 1) * (T.L q).card ≤ 2 ^ (n - 1) * (T.L T.h).card := by
    have := T.L_pow (n - 1) (by omega)
    rwa [show T.h - (n - 1) = q by omega] at this
  have hn1 := num1 n hn
  have hKθ : K * θ * (T.L q).card ≤ (T.L T.h).card := by
    have h3 : 0 < 3 ^ (n - 1) := by positivity
    have : 3 ^ (n - 1) * (K * θ * (T.L q).card) ≤ 3 ^ (n - 1) * (T.L T.h).card := by
      calc 3 ^ (n - 1) * (K * θ * (T.L q).card) = (K * θ) * (3 ^ (n - 1) * (T.L q).card) := by ring
        _ ≤ (K * θ) * (2 ^ (n - 1) * (T.L T.h).card) := Nat.mul_le_mul_left _ hLq
        _ = (K * θ * 2 ^ (n - 1)) * (T.L T.h).card := by ring
        _ ≤ 3 ^ (n - 1) * (T.L T.h).card := Nat.mul_le_mul_right _ hn1
    exact Nat.le_of_mul_le_mul_left this h3
  have : K * Z.card ≤ 2 * (T.L T.h).card := by omega
  have : 2 * (T.L T.h).card < K * Z.card := by
    have : 2 * (16 * n ^ 2 * (n + 1) * Z.card) = K * Z.card := by ring
    omega
  omega

end HTree

end Claim34c




section TreeCycles

variable {V : Type} {G : SimpleGraph V}

lemma cycle_of_list (L : List V) (hn : L.Nodup) (hc : L.IsChain G.Adj) (hl : 3 ≤ L.length)
    (hne : L ≠ []) (hclose : G.Adj (L.getLast hne) (L.head hne)) : L.length ∈ G.cycleLengths := by
  set x0 := L.head hne
  let g : ℕ → V := fun i => L.getD i x0
  have hg : ∀ i (hi : i < L.length), g i = L[i] := fun i hi => List.getD_eq_getElem _ _ hi
  apply cycle_of_fun G L.length hl g
  · intro i hi
    rw [hg i (by omega), hg (i + 1) hi]
    exact (List.isChain_iff_getElem.mp hc) i hi
  · rw [hg _ (by omega), hg 0 (by omega)]
    rw [List.getLast_eq_getElem] at hclose
    rw [show x0 = L[0] from List.head_eq_getElem hne] at hclose
    exact hclose
  · intro i j hi hj e
    rw [hg i hi, hg j hj] at e
    exact (List.Nodup.getElem_inj_iff hn).mp e

variable (par : V → V) (lev : V → ℕ)

/-- `[v, par v, …, par^[s-1] v]` -/
def upL (v : V) (s : ℕ) : List V := (List.range s).map (fun i => par^[i] v)

lemma upL_length (v : V) (s : ℕ) : (upL par v s).length = s := by simp [upL]

lemma mem_upL {v x : V} {s : ℕ} : x ∈ upL par v s ↔ ∃ i < s, par^[i] v = x := by
  simp only [upL, List.mem_map, List.mem_range]

lemma upL_succ (v : V) (s : ℕ) : upL par v (s + 1) = upL par v s ++ [par^[s] v] := by
  rw [upL, upL, List.range_succ, List.map_append]; rfl

variable {par lev}

lemma upL_chain (hP : IsParent G par lev) (v : V) (s : ℕ) (hs : s ≤ lev v + 1) :
    (upL par v s).IsChain G.Adj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [upL, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hi ⊢
  exact adj_iter hP i v (by omega)

lemma upL_nodup (hP : IsParent G par lev) (v : V) (s : ℕ) (hs : s ≤ lev v + 1) :
    (upL par v s).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj e
  simp only [List.mem_range] at hi hj
  have h1 := lev_iter hP i v (by omega)
  have h2 := lev_iter hP j v (by omega)
  rw [e] at h1
  omega

/-- A tree path through the common ancestor plus an outside list closes a cycle. -/
lemma tree_list_cycle (hP : IsParent G par lev) (z z' : V) (α : ℕ) (hα : 1 ≤ α)
    (hz : α ≤ lev z) (hz' : lev z' = lev z)
    (heq : par^[α] z = par^[α] z') (hne : par^[α - 1] z ≠ par^[α - 1] z')
    (M : List V) (hM : M ≠ []) (hMn : M.Nodup) (hMc : M.IsChain G.Adj)
    (hMdisj : ∀ x ∈ M, ∀ i, i ≤ α → x ≠ par^[i] z ∧ x ≠ par^[i] z')
    (hstart : G.Adj z' (M.head hM)) (hend : G.Adj (M.getLast hM) z) :
    2 * α + 1 + M.length ∈ G.cycleLengths := by
  have hz'' : α ≤ lev z' := by rw [hz']; exact hz
  set UL := upL par z α ++ [par^[α] z] ++ (upL par z' α).reverse with hUL
  have hULlen : UL.length = 2 * α + 1 := by simp [UL, upL_length]; ring
  -- chain of UL
  have hULc : UL.IsChain G.Adj := by
    have h1 : (upL par z α ++ [par^[α] z]).IsChain G.Adj := by
      rw [← upL_succ]; exact upL_chain hP z (α + 1) (by omega)
    have h2 : (upL par z' α).reverse.IsChain G.Adj := by
      rw [List.isChain_reverse]
      have := upL_chain hP z' α (by omega)
      exact this.imp (fun a b h => h.symm)
    apply h1.append h2
    intro x hx y hy
    rw [List.getLast?_append, List.getLast?_singleton] at hx
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_reverse] at hy
    rw [← hx]
    have hlast : (upL par z' α).getLast? = some (par^[α - 1] z') := by
      rw [show α = (α - 1) + 1 by omega, upL_succ, List.getLast?_append, List.getLast?_singleton]
      simp
    rw [hlast, Option.mem_def, Option.some.injEq] at hy
    rw [← hy, heq]
    have := adj_iter hP (α - 1) z' (by omega)
    rw [show α - 1 + 1 = α by omega] at this
    exact this.symm
  -- nodup of UL
  have hULn : UL.Nodup := by
    have hlv : ∀ i, i ≤ α → lev (par^[i] z) = lev z - i := fun i hi => lev_iter hP i z (by omega)
    have hlv' : ∀ i, i ≤ α → lev (par^[i] z') = lev z - i := fun i hi => by
      rw [lev_iter hP i z' (by omega), hz']
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨upL_nodup hP z α (by omega), List.nodup_singleton _, ?_⟩,
      List.nodup_reverse.mpr (upL_nodup hP z' α (by omega)), ?_⟩
    · intro a ha b hb e
      rw [List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp ha
      have := congrArg lev (e.trans hb)
      rw [hlv i (by omega), hlv α le_rfl] at this; omega
    · intro a ha b hb e
      rw [List.mem_reverse] at hb
      obtain ⟨j, hj, rfl⟩ := (mem_upL par).mp hb
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp ha
        have hl := congrArg lev e
        rw [hlv i (by omega), hlv' j (by omega)] at hl
        have hij : i = j := by omega
        subst hij
        exact iter_ne_of_ne z z' (show i ≤ α - 1 by omega) hne e
      · subst ha
        have hl := congrArg lev e
        rw [hlv α le_rfl, hlv' j (by omega)] at hl; omega
  have hULne : UL ≠ [] := by intro h; have := congrArg List.length h; simp [hULlen] at this
  have hULhead : UL.head hULne = z := by
    simp only [UL, upL]
    rcases α with _ | α
    · omega
    · simp [List.range_succ_eq_map]
  have hrne : (upL par z' α).reverse ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_reverse, upL_length]; omega)
  have hULlast : UL.getLast hULne = z' := by
    simp only [UL]
    rw [List.getLast_append_of_ne_nil _ hrne, List.getLast_reverse]
    simp only [upL]
    rcases α with _ | α
    · omega
    · simp [List.range_succ_eq_map]
  have hdisj : ∀ x ∈ UL, x ∉ M := by
    intro x hx hxM
    rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_reverse] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp hx
      exact (hMdisj _ hxM i (by omega)).1 rfl
    · subst hx; exact (hMdisj _ hxM α le_rfl).1 rfl
    · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp hx
      exact (hMdisj _ hxM i (by omega)).2 rfl
  have hC := cycle_of_list (G := G) (UL ++ M) ?_ ?_ (by simp [hULlen]; omega) (by simp [hULne]) ?_
  · simpa [hULlen] using hC
  · rw [List.nodup_append]
    exact ⟨hULn, hMn, fun a ha b hb e => hdisj a ha (e ▸ hb)⟩
  · apply hULc.append hMc
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast hULne, Option.mem_def, Option.some.injEq, hULlast] at hx
    rw [List.head?_eq_some_head hM, Option.mem_def, Option.some.injEq] at hy
    rw [← hx, ← hy]; exact hstart
  · rw [List.getLast_append_of_ne_nil _ hM, List.head_append_of_ne_nil hULne, hULhead]
    exact hend

end TreeCycles



section Vee

variable {V : Type} {G : SimpleGraph V} {par : V → V} {lev : V → ℕ}

/-- the tree path `z → common ancestor → z'` as a list -/
def vee (par : V → V) (z z' : V) (α : ℕ) : List V := upL par z α ++ [par^[α] z] ++ (upL par z' α).reverse

lemma vee_props (hP : IsParent G par lev) (z z' : V) (α : ℕ) (hz : α ≤ lev z) (hz' : lev z' = lev z)
    (heq : par^[α] z = par^[α] z') (hne : 1 ≤ α → par^[α - 1] z ≠ par^[α - 1] z') :
    (vee par z z' α).length = 2 * α + 1 ∧ (vee par z z' α).IsChain G.Adj ∧ (vee par z z' α).Nodup ∧
    (vee par z z' α).head? = some z ∧ (vee par z z' α).getLast? = some z' ∧
    (∀ x ∈ vee par z z' α, ∃ i, i ≤ α ∧ (x = par^[i] z ∨ x = par^[i] z')) := by
  have hz'' : α ≤ lev z' := by rw [hz']; exact hz
  have hlv : ∀ i, i ≤ α → lev (par^[i] z) = lev z - i := fun i hi => lev_iter hP i z (by omega)
  have hlv' : ∀ i, i ≤ α → lev (par^[i] z') = lev z - i := fun i hi => by
    rw [lev_iter hP i z' (by omega), hz']
  refine ⟨by simp [vee, upL_length]; ring, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (upL par z α ++ [par^[α] z]).IsChain G.Adj := by
      rw [← upL_succ]; exact upL_chain hP z (α + 1) (by omega)
    have h2 : (upL par z' α).reverse.IsChain G.Adj := by
      rw [List.isChain_reverse]
      exact (upL_chain hP z' α (by omega)).imp (fun a b h => h.symm)
    apply h1.append h2
    intro x hx y hy
    rw [List.getLast?_append, List.getLast?_singleton] at hx
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_reverse] at hy
    rcases Nat.eq_zero_or_pos α with h0 | hpos
    · subst h0; simp [upL] at hy
    have hlast : (upL par z' α).getLast? = some (par^[α - 1] z') := by
      rw [show α = (α - 1) + 1 by omega, upL_succ, List.getLast?_append, List.getLast?_singleton]
      simp
    rw [hlast, Option.mem_def, Option.some.injEq] at hy
    rw [← hx, ← hy, heq]
    have := adj_iter hP (α - 1) z' (by omega)
    rw [show α - 1 + 1 = α by omega] at this
    exact this.symm
  · rw [vee, List.nodup_append, List.nodup_append]
    refine ⟨⟨upL_nodup hP z α (by omega), List.nodup_singleton _, ?_⟩,
      List.nodup_reverse.mpr (upL_nodup hP z' α (by omega)), ?_⟩
    · intro a ha b hb e
      rw [List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp ha
      have := congrArg lev (e.trans hb)
      rw [hlv i (by omega), hlv α le_rfl] at this; omega
    · intro a ha b hb e
      rw [List.mem_reverse] at hb
      obtain ⟨j, hj, rfl⟩ := (mem_upL par).mp hb
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp ha
        have hl := congrArg lev e
        rw [hlv i (by omega), hlv' j (by omega)] at hl
        have hij : i = j := by omega
        subst hij
        exact iter_ne_of_ne z z' (show i ≤ α - 1 by omega) (hne (by omega)) e
      · subst ha
        have hl := congrArg lev e
        rw [hlv α le_rfl, hlv' j (by omega)] at hl; omega
  · rcases Nat.eq_zero_or_pos α with h0 | hpos
    · subst h0; simp [vee, upL]
    · rw [vee, List.append_assoc, List.head?_append]
      obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
      simp [upL, List.range_succ_eq_map]
  · rcases Nat.eq_zero_or_pos α with h0 | hpos
    · subst h0; simp [vee, upL]; simpa using heq
    · rw [vee, List.getLast?_append, List.getLast?_reverse]
      obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
      simp [upL, List.range_succ_eq_map]
  · intro x hx
    rw [vee, List.mem_append, List.mem_append, List.mem_singleton, List.mem_reverse] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp hx; exact ⟨i, by omega, Or.inl rfl⟩
    · exact ⟨α, le_rfl, Or.inl hx⟩
    · obtain ⟨i, hi, rfl⟩ := (mem_upL par).mp hx; exact ⟨i, by omega, Or.inr rfl⟩

/-- optional center -/
def optL : Option V → List V
  | none => []
  | some y => [y]

/-- the quad cycle: tree path `z…z'`, join to `b`, tree path `b…a`, join back to `z` -/
lemma quad_cycle (hP : IsParent G par lev) (z z' a b : V) (α β : ℕ) (hα : 1 ≤ α)
    (hz : α ≤ lev z) (hz' : lev z' = lev z) (heq : par^[α] z = par^[α] z')
    (hne : par^[α - 1] z ≠ par^[α - 1] z')
    (hb : β ≤ lev b) (ha : lev a = lev b) (heq' : par^[β] b = par^[β] a)
    (hne' : 1 ≤ β → par^[β - 1] b ≠ par^[β - 1] a)
    (c1 c2 : Option V)
    -- the joins
    (hj2 : ∀ y, c2 = some y → G.Adj z' y ∧ G.Adj y b) (hj2' : c2 = none → G.Adj z' b)
    (hj1 : ∀ y, c1 = some y → G.Adj a y ∧ G.Adj y z) (hj1' : c1 = none → G.Adj a z)
    (hcen : ∀ y, c1 = some y → c2 ≠ some y)
    -- separation
    (hsep : ∀ i, i ≤ α → ∀ j, j ≤ β → par^[i] z ≠ par^[j] b ∧ par^[i] z ≠ par^[j] a ∧
      par^[i] z' ≠ par^[j] b ∧ par^[i] z' ≠ par^[j] a)
    (hcz : ∀ y, (c1 = some y ∨ c2 = some y) → ∀ i, i ≤ α → y ≠ par^[i] z ∧ y ≠ par^[i] z')
    (hcb : ∀ y, (c1 = some y ∨ c2 = some y) → ∀ j, j ≤ β → y ≠ par^[j] b ∧ y ≠ par^[j] a) :
    2 * α + 2 * β + 2 + (optL c1).length + (optL c2).length ∈ G.cycleLengths := by
  obtain ⟨hl, hc, hn, hh, hlast, hmem⟩ := vee_props hP b a β hb ha heq' hne'
  set M := optL c2 ++ vee par b a β ++ optL c1 with hM
  have hMne : M ≠ [] := by
    intro h; have := congrArg List.length h; simp [M, hl] at this
  have hvne : vee par b a β ≠ [] := by
    intro h; rw [h] at hl; simp at hl
  have key := tree_list_cycle hP z z' α hα hz hz' heq hne M hMne ?_ ?_ ?_ ?_ ?_
  · have : M.length = (optL c2).length + (2 * β + 1) + (optL c1).length := by simp [M, hl]; omega
    rw [this] at key
    convert key using 1; ring
  · -- nodup
    rw [hM, List.nodup_append, List.nodup_append]
    refine ⟨⟨?_, hn, ?_⟩, ?_, ?_⟩
    · cases c2 <;> simp [optL]
    · intro x hx y hy e
      cases c2 with
      | none => simp [optL] at hx
      | some y2 =>
        simp only [optL, List.mem_singleton] at hx
        subst hx; subst e
        obtain ⟨j, hj, hj'⟩ := hmem _ hy
        rcases hj' with h | h
        · exact (hcb _ (Or.inr rfl) j hj).1 h
        · exact (hcb _ (Or.inr rfl) j hj).2 h
    · cases c1 <;> simp [optL]
    · intro x hx y hy e
      cases c1 with
      | none => simp [optL] at hy
      | some y1 =>
        simp only [optL, List.mem_singleton] at hy
        subst hy; subst e
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · cases c2 with
          | none => simp [optL] at hx
          | some y2 =>
            simp only [optL, List.mem_singleton] at hx
            exact hcen _ rfl (by rw [hx])
        · obtain ⟨j, hj, hj'⟩ := hmem _ hx
          rcases hj' with h | h
          · exact (hcb _ (Or.inl rfl) j hj).1 h
          · exact (hcb _ (Or.inl rfl) j hj).2 h
  · -- chain
    rw [hM]
    apply List.IsChain.append
    · apply List.IsChain.append
      · cases c2 <;> simp [optL]
      · exact hc
      · intro x hx y hy
        cases c2 with
        | none => simp [optL] at hx
        | some y2 =>
          simp only [optL, List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          rw [hh, Option.mem_def, Option.some.injEq] at hy
          rw [← hx, ← hy]; exact (hj2 y2 rfl).2
    · cases c1 <;> simp [optL]
    · intro x hx y hy
      cases c1 with
      | none => simp [optL] at hy
      | some y1 =>
        simp only [optL, List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
        rw [List.getLast?_append, hlast] at hx
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx
        rw [← hx, ← hy]; exact (hj1 y1 rfl).1
  · -- disjoint
    intro x hx i hi
    rw [hM, List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · cases c2 with
      | none => simp [optL] at hx
      | some y2 =>
        simp only [optL, List.mem_singleton] at hx
        subst hx; exact hcz _ (Or.inr rfl) i hi
    · obtain ⟨j, hj, hj'⟩ := hmem _ hx
      rcases hj' with h | h <;> subst h
      · exact ⟨fun e => (hsep i hi j hj).1 e.symm, fun e => (hsep i hi j hj).2.2.1 e.symm⟩
      · exact ⟨fun e => (hsep i hi j hj).2.1 e.symm, fun e => (hsep i hi j hj).2.2.2 e.symm⟩
    · cases c1 with
      | none => simp [optL] at hx
      | some y1 =>
        simp only [optL, List.mem_singleton] at hx
        subst hx; exact hcz _ (Or.inl rfl) i hi
  · -- start
    have hx := List.head?_eq_some_head hMne
    generalize M.head hMne = x at hx ⊢
    rw [hM, List.append_assoc, List.head?_append, List.head?_append, hh] at hx
    cases c2 with
    | none =>
      simp [optL] at hx
      rw [← hx]; exact hj2' rfl
    | some y =>
      simp [optL] at hx
      rw [← hx]; exact (hj2 y rfl).1
  · -- end
    have hx := List.getLast?_eq_getLast hMne
    generalize M.getLast hMne = x at hx ⊢
    rw [hM, List.getLast?_append, List.getLast?_append, hlast] at hx
    cases c1 with
    | none =>
      simp [optL] at hx
      rw [← hx]; exact hj1' rfl
    | some y =>
      simp [optL] at hx
      rw [← hx]; exact (hj1 y rfl).2

end Vee






section CountCore

variable {V : Type} [Fintype V]

/-- a finite set of naturals has a parity class of at least half its size -/
lemma parity_half (J : Finset ℕ) : ∃ p : Bool, J.card ≤ 2 * (J.filter (fun i => decide (Even i) = p)).card := by
  have h : (J.filter (fun i => decide (Even i) = true)).card +
      (J.filter (fun i => ¬ (decide (Even i) = true))).card = J.card :=
    Finset.card_filter_add_card_filter_not _
  have e : J.filter (fun i => ¬ (decide (Even i) = true)) = J.filter (fun i => decide (Even i) = false) := by
    congr 1; ext i; simp
  rw [e] at h
  by_cases hle : (J.filter (fun i => decide (Even i) = false)).card ≤
      (J.filter (fun i => decide (Even i) = true)).card
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

lemma parity_gap {i i' : ℕ} {p : Bool} (h1 : decide (Even i) = p) (h2 : decide (Even i') = p)
    (hlt : i < i') : i + 2 ≤ i' := by
  by_contra h
  have : i' = i + 1 := by omega
  subst this
  have e : decide (Even (i + 1)) = !decide (Even i) := by
    by_cases he : Even i <;> simp [he, Nat.even_add_one]
  rw [e, h1] at h2
  cases p <;> simp at h2

lemma optL_len (c : Option V) : (optL c).length ≤ 1 := by cases c <;> simp [optL]

/-- The combinatorial core of GKS Claim 5 and the count of distinct cycle lengths. -/
lemma count_core (n : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i + 1 < n) (zf : ℕ → V)
    (R : V → V → Prop) (JV : V → V → Option V → Prop) (β : V → V → ℕ)
    (hβsymm : ∀ x y, β x y = β y x) (hβultra : ∀ x y z, β x z ≤ max (β x y) (β y z))
    (hβle : ∀ x y, β x y ≤ n) (Λ : Set ℕ)
    (hquad : ∀ i ∈ I, ∀ j, (j ∈ I ∨ j = n - 1) → i < j → ∀ a b c1 c2, R (zf i) a → R (zf j) b →
      JV (zf i) a c1 → JV (zf j) b c2 → (∀ y, c1 = some y → c2 ≠ some y) →
      2 * (n - 1 - i) + 2 * β a b + 2 + (optL c1).length + (optL c2).length ∈ Λ)
    (hc2 : ∀ j ∈ I, ∀ v a b, R (zf j) a → JV (zf j) a (some v) → R (zf (n - 1)) b →
      JV (zf (n - 1)) b (some v) → 2 * (n - 1 - j) + 2 ∈ Λ)
    (hreroute : ∀ i ∈ I, ∀ κ, (κ ∈ I ∨ κ = n - 1) → i < κ → ∀ a x y, R (zf i) a →
      JV (zf i) a (some y) → R (zf κ) x → JV (zf κ) x (some y) → R (zf i) x ∧ JV (zf i) x (some y))
    (hne : ∀ i, (i ∈ I ∨ i = n - 1) → ∃ t c, R (zf i) t ∧ JV (zf i) t c) :
    ∃ Λ' : Finset ℕ, (∀ ℓ ∈ Λ', ℓ ∈ Λ ∧ ℓ ≤ 4 * n + 4) ∧ I.card ≤ 3 * Λ'.card + 1 := by
  classical
  -- valid configurations
  let valid : ℕ → ℕ × V × V × Option V × Option V → Prop := fun i C =>
    (C.1 ∈ I ∨ C.1 = n - 1) ∧ i < C.1 ∧ R (zf i) C.2.1 ∧ R (zf C.1) C.2.2.1 ∧
      JV (zf i) C.2.1 C.2.2.2.1 ∧ JV (zf C.1) C.2.2.1 C.2.2.2.2 ∧
      (∀ y, C.2.2.2.1 = some y → C.2.2.2.2 ≠ some y)
  let Conf : ℕ → Finset (ℕ × V × V × Option V × Option V) := fun i =>
    ((Finset.range n) ×ˢ Finset.univ).filter (valid i)
  have hmemC : ∀ i, i ∈ I → ∀ C, valid i C → C ∈ Conf i := by
    intro i hi C hC
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩, hC⟩
    rcases hC.1 with h | h
    · have := hI _ h; omega
    · have := hI i hi; omega
  let bet : ℕ × V × V × Option V × Option V → ℕ := fun C => β C.2.1 C.2.2.1
  let lenC : ℕ → ℕ × V × V × Option V × Option V → ℕ := fun i C =>
    2 * (n - 1 - i) + 2 * bet C + 2 + (optL C.2.2.2.1).length + (optL C.2.2.2.2).length
  have hlenΛ : ∀ i ∈ I, ∀ C ∈ Conf i, lenC i C ∈ Λ := by
    intro i hi C hC
    obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := Finset.mem_filter.mp hC
    exact hquad i hi C.1 h1 h2 C.2.1 C.2.2.1 C.2.2.2.1 C.2.2.2.2 h3 h4 h5 h6 h7
  have hlenle : ∀ i C, lenC i C ≤ 4 * n + 4 := by
    intro i C
    have := hβle C.2.1 C.2.2.1
    have := optL_len C.2.2.2.1
    have := optL_len C.2.2.2.2
    simp only [lenC, bet]; omega
  -- Claim 5
  have claim5 : ∀ i ∈ I, ∀ i' ∈ I, i < i' → ∀ C ∈ Conf i, (∀ C'' ∈ Conf i, bet C'' ≤ bet C) →
      ∀ C' ∈ Conf i', bet C' ≤ bet C := by
    intro i hi i' hi' hii C hC hmax C' hC'
    obtain ⟨_, hj, hij, ha, hb, hc1, hc2', hv⟩ := Finset.mem_filter.mp hC
    obtain ⟨_, hj', hij', ha', hb', hc1', hc2'', hv'⟩ := Finset.mem_filter.mp hC'
    by_contra hlt
    push Not at hlt
    simp only [bet] at hlt
    set a := C.2.1; set b := C.2.2.1; set a' := C'.2.1; set b' := C'.2.2.1
    -- some endpoint x' of C' is far from a
    have hu := hβultra a' a b'
    rw [hβsymm a' a] at hu
    -- the rerouting argument for a target x of index κ with center cx
    have key : ∀ κ x cx, (κ ∈ I ∨ κ = n - 1) → i < κ → R (zf κ) x → JV (zf κ) x cx →
        β a b < β a x → False := by
      intro κ x cx hκ hiκ hRx hJx hfar
      have hfar2 : β a b < β x b := by
        have := hβultra a b x
        rw [hβsymm b x] at this
        have := hβultra a x b
        by_contra h; push Not at h
        have h3 := hβultra a b x
        rw [hβsymm b x] at h3
        omega
      by_cases hval : ∀ y, C.2.2.2.1 = some y → cx ≠ some y
      · have hT : (κ, a, x, C.2.2.2.1, cx) ∈ Conf i :=
          hmemC i hi _ ⟨hκ, hiκ, ha, hRx, hc1, hJx, hval⟩
        have := hmax _ hT
        change β a x ≤ β a b at this
        omega
      · push Not at hval
        obtain ⟨y, hy1, hy2⟩ := hval
        rw [hy1] at hc1
        rw [hy2] at hJx
        obtain ⟨hRix, hJix⟩ := hreroute i hi κ hκ hiκ a x y ha hc1 hRx hJx
        have hval2 : ∀ y', some y = some y' → C.2.2.2.2 ≠ some y' := by
          intro y' e; rw [← Option.some.inj e]; exact hv y hy1
        have hT : (C.1, x, b, some y, C.2.2.2.2) ∈ Conf i :=
          hmemC i hi _ ⟨hj, hij, hRix, hb, hJix, hc2', hval2⟩
        have := hmax _ hT
        change β x b ≤ β a b at this
        omega
    have hia : i < i' := hii
    have hib : i < C'.1 := lt_trans hii hij'
    have hI'1 : i' ∈ I ∨ i' = n - 1 := Or.inl hi'
    by_cases h1 : β a b < β a a'
    · exact key i' a' C'.2.2.2.1 hI'1 hia ha' hc1' h1
    · have h2 : β a b < β a b' := by
        push Not at h1
        by_contra h2; push Not at h2
        have : max (β a a') (β a b') ≤ β a b := max_le h1 h2
        omega
      exact key C'.1 b' C'.2.2.2.2 hj' hib hb' hc2'' h2
  -- good indices and their best configurations
  let Good := I.filter (fun i => (Conf i).Nonempty)
  have hbest : ∀ i ∈ Good, ∃ C ∈ Conf i, ∀ C'' ∈ Conf i, bet C'' ≤ bet C := by
    intro i hi
    exact Finset.exists_max_image _ bet (Finset.mem_filter.mp hi).2
  let best : ℕ → ℕ × V × V × Option V × Option V := fun i =>
    if h : i ∈ Good then Classical.choose (hbest i h) else (0, zf 0, zf 0, none, none)
  have hbestspec : ∀ i ∈ Good, best i ∈ Conf i ∧ ∀ C'' ∈ Conf i, bet C'' ≤ bet (best i) := by
    intro i hi
    simp only [best, dif_pos hi]
    exact Classical.choose_spec (hbest i hi)
  let Len : ℕ → ℕ := fun i => lenC i (best i)
  -- strict decrease along a parity class of good indices
  have hdec : ∀ i ∈ Good, ∀ i' ∈ Good, i + 2 ≤ i' → Len i' < Len i := by
    intro i hi i' hi' hle
    have hiI := (Finset.mem_filter.mp hi).1
    have hi'I := (Finset.mem_filter.mp hi').1
    obtain ⟨hC, hmax⟩ := hbestspec i hi
    obtain ⟨hC', _⟩ := hbestspec i' hi'
    have h5 := claim5 i hiI i' hi'I (by omega) (best i) hC hmax (best i') hC'
    have h6 := hI i' hi'I
    have := optL_len (best i).2.2.2.1
    have := optL_len (best i).2.2.2.2
    have := optL_len (best i').2.2.2.1
    have := optL_len (best i').2.2.2.2
    simp only [Len, lenC]
    omega
  have hparity : ∀ J ⊆ Good, ∃ Λ1 : Finset ℕ, (∀ ℓ ∈ Λ1, ℓ ∈ Λ ∧ ℓ ≤ 4 * n + 4) ∧
      J.card ≤ 2 * Λ1.card := by
    intro J hJ
    obtain ⟨p, hp⟩ := parity_half J
    refine ⟨(J.filter (fun i => decide (Even i) = p)).image Len, ?_, ?_⟩
    · intro ℓ hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
      have hiG := hJ (Finset.mem_filter.mp hi).1
      exact ⟨hlenΛ i (Finset.mem_filter.mp hiG).1 _ (hbestspec i hiG).1, hlenle _ _⟩
    · rw [Finset.card_image_of_injOn]
      · exact hp
      · intro i hi i' hi' e
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hi'
        by_contra hne'
        rcases lt_or_gt_of_ne hne' with h | h
        · have := hdec i (hJ hi.1) i' (hJ hi'.1) (parity_gap hi.2 hi'.2 h)
          omega
        · have := hdec i' (hJ hi'.1) i (hJ hi.1) (parity_gap hi'.2 hi.2 h)
          omega
  by_cases hall : I ⊆ Good
  · obtain ⟨Λ1, h1, h2⟩ := hparity I hall
    exact ⟨Λ1, h1, by omega⟩
  · -- the first bad index
    have hbad : (I.filter (fun i => i ∉ Good)).Nonempty := by
      rw [Finset.not_subset] at hall
      obtain ⟨i, hi, hig⟩ := hall
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hig⟩⟩
    set i0 := (I.filter (fun i => i ∉ Good)).min' hbad
    have hi0 := Finset.min'_mem _ hbad
    have hi0I := (Finset.mem_filter.mp hi0).1
    have hi0G := (Finset.mem_filter.mp hi0).2
    have hConf0 : Conf i0 = ∅ := by
      by_contra h
      exact hi0G (Finset.mem_filter.mpr ⟨hi0I, Finset.nonempty_iff_ne_empty.mpr h⟩)
    have hlow : I.filter (· < i0) ⊆ Good := by
      intro i hi
      obtain ⟨hiI, hlt⟩ := Finset.mem_filter.mp hi
      by_contra hG
      have := Finset.min'_le (I.filter (fun i => i ∉ Good)) i (Finset.mem_filter.mpr ⟨hiI, hG⟩)
      omega
    -- the common center
    obtain ⟨a0, c0, hRa0, hJa0⟩ := hne i0 (Or.inl hi0I)
    obtain ⟨bl, cl, hRbl, hJbl⟩ := hne (n - 1) (Or.inr rfl)
    have hi0n := hI i0 hi0I
    have hinv : ∀ j b c, (j ∈ I ∨ j = n - 1) → i0 < j → R (zf j) b → JV (zf j) b c →
        ∃ y, c0 = some y ∧ c = some y := by
      intro j b c hj hij hR hJ
      by_contra hcon
      push Not at hcon
      have hT : (j, a0, b, c0, c) ∈ Conf i0 :=
        hmemC i0 hi0I _ ⟨hj, hij, hRa0, hR, hJa0, hJ, fun y h1 h2 => hcon y h1 h2⟩
      rw [hConf0] at hT; simp at hT
    obtain ⟨v, hc0v, hclv⟩ := hinv (n - 1) bl cl (Or.inr rfl) (by omega) hRbl hJbl
    rw [hclv] at hJbl
    have hC2 : ∀ j ∈ I, i0 ≤ j → 2 * (n - 1 - j) + 2 ∈ Λ := by
      intro j hj hij
      rcases eq_or_lt_of_le hij with h | h
      · rw [← h]; rw [hc0v] at hJa0; exact hc2 i0 hi0I v a0 bl hRa0 hJa0 hRbl hJbl
      · obtain ⟨bj, cj, hRbj, hJbj⟩ := hne j (Or.inl hj)
        obtain ⟨y, hy0, hyj⟩ := hinv j bj cj (Or.inl hj) h hRbj hJbj
        rw [hc0v] at hy0
        cases hy0
        rw [hyj] at hJbj
        exact hc2 j hj v bj bl hRbj hJbj hRbl hJbl
    obtain ⟨Λ1, h1, h2⟩ := hparity _ hlow
    set Λ2 := (I.filter (i0 ≤ ·)).image (fun j => 2 * (n - 1 - j) + 2)
    have hΛ2 : ∀ ℓ ∈ Λ2, ℓ ∈ Λ ∧ ℓ ≤ 4 * n + 4 := by
      intro ℓ hℓ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨hjI, hij⟩ := Finset.mem_filter.mp hj
      exact ⟨hC2 j hjI hij, by omega⟩
    have hΛ2card : Λ2.card = (I.filter (i0 ≤ ·)).card := by
      apply Finset.card_image_of_injOn
      intro j hj j' hj' e
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj hj'
      have := hI j hj.1; have := hI j' hj'.1
      beta_reduce at e; omega
    have hsplit : I.card = (I.filter (· < i0)).card + (I.filter (i0 ≤ ·)).card := by
      rw [← Finset.card_filter_add_card_filter_not (fun i => i < i0)]
      congr 2; ext i; simp
    by_cases hc : Λ2.card ≤ Λ1.card
    · exact ⟨Λ1, h1, by omega⟩
    · exact ⟨Λ2, hΛ2, by omega⟩

end CountCore


section T1final

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- join with an explicit center -/
def JVc (CGr : SimpleGraph V) (Y : Finset V) (x t : V) (cen : Option V) : Prop :=
  (cen = none ∧ CGr.Adj x t) ∨ (∃ y, cen = some y ∧ y ∈ Y ∧ CGr.Adj x y ∧ CGr.Adj y t)

lemma JVc_some {CGr : SimpleGraph V} {Y : Finset V} {x t y : V} (h : JVc CGr Y x t (some y)) :
    y ∈ Y ∧ CGr.Adj x y ∧ CGr.Adj y t := by
  rcases h with ⟨h1, _⟩ | ⟨y', h1, h2⟩
  · cases h1
  · cases h1; exact h2

lemma JVc_none {CGr : SimpleGraph V} {Y : Finset V} {x t : V} (h : JVc CGr Y x t none) :
    CGr.Adj x t := by
  rcases h with ⟨_, h1⟩ | ⟨y', h1, _⟩
  · exact h1
  · cases h1

/-- first common iterate, capped at `N` -/
def fβ (par : V → V) (N : ℕ) (a b : V) : ℕ :=
  if h : ∃ s, par^[s] a = par^[s] b then min N (Nat.find h) else N

lemma fβ_le (par : V → V) (N : ℕ) (a b : V) : fβ par N a b ≤ N := by
  unfold fβ; split_ifs <;> omega

lemma fβ_symm (par : V → V) (N : ℕ) (a b : V) : fβ par N a b = fβ par N b a := by
  unfold fβ
  have e : (∃ s, par^[s] a = par^[s] b) ↔ (∃ s, par^[s] b = par^[s] a) :=
    ⟨fun ⟨s, h⟩ => ⟨s, h.symm⟩, fun ⟨s, h⟩ => ⟨s, h.symm⟩⟩
  by_cases h : ∃ s, par^[s] a = par^[s] b
  · have h' := e.mp h
    rw [dif_pos h, dif_pos h']
    congr 1
    apply le_antisymm
    · exact Nat.find_min' h (Nat.find_spec h').symm
    · exact Nat.find_min' h' (Nat.find_spec h).symm
  · have h' : ¬ ∃ s, par^[s] b = par^[s] a := fun h'' => h (e.mpr h'')
    rw [dif_neg h, dif_neg h']

lemma iter_eq_mono (par : V → V) {a b : V} {s s' : ℕ} (hs : s ≤ s') (h : par^[s] a = par^[s] b) :
    par^[s'] a = par^[s'] b := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_add_apply, h]

lemma fβ_ultra (par : V → V) (N : ℕ) (x y z : V) :
    fβ par N x z ≤ max (fβ par N x y) (fβ par N y z) := by
  unfold fβ
  by_cases h1 : ∃ s, par^[s] x = par^[s] y
  · by_cases h2 : ∃ s, par^[s] y = par^[s] z
    · have h3 : ∃ s, par^[s] x = par^[s] z := ⟨max (Nat.find h1) (Nat.find h2),
        (iter_eq_mono par (le_max_left _ _) (Nat.find_spec h1)).trans
          (iter_eq_mono par (le_max_right _ _) (Nat.find_spec h2))⟩
      rw [dif_pos h1, dif_pos h2, dif_pos h3]
      have : Nat.find h3 ≤ max (Nat.find h1) (Nat.find h2) := Nat.find_min' h3
        ((iter_eq_mono par (le_max_left _ _) (Nat.find_spec h1)).trans
          (iter_eq_mono par (le_max_right _ _) (Nat.find_spec h2)))
      omega
    · rw [dif_neg h2]; split_ifs <;> omega
  · rw [dif_neg h1]; split_ifs <;> omega

lemma fβ_spec (par : V → V) (N : ℕ) (a b : V) (s0 : ℕ) (hs0 : s0 ≤ N) (h0 : par^[s0] a = par^[s0] b) :
    fβ par N a b ≤ s0 ∧ par^[fβ par N a b] a = par^[fβ par N a b] b ∧
      (1 ≤ fβ par N a b → par^[fβ par N a b - 1] a ≠ par^[fβ par N a b - 1] b) := by
  have h : ∃ s, par^[s] a = par^[s] b := ⟨s0, h0⟩
  have hle : Nat.find h ≤ s0 := Nat.find_min' h h0
  have e : fβ par N a b = Nat.find h := by unfold fβ; rw [dif_pos h]; omega
  rw [e]
  exact ⟨hle, Nat.find_spec h, fun h1 => Nat.find_min h (by omega)⟩

end T1final


section T1main

/-- weight from many distinct bounded lengths -/
lemma weight_of_set {V : Type} [Fintype V] (G : SimpleGraph V) (Λ' : Finset ℕ) (M A : ℕ) (hM : 1 ≤ M)
    (hΛ : ∀ ℓ ∈ Λ', ℓ ∈ G.cycleLengths ∧ ℓ ≤ M) :
    ((Λ'.card : ℝ) - A) / M ≤ wAbove G A := by
  have hsub : Λ'.filter (A < ·) ⊆ (CF G).filter (A < ·) := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hℓ
    refine Finset.mem_filter.mpr ⟨?_, h2⟩
    simp only [CF, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (cycleLengths_le_card G (hΛ ℓ h1).1), (hΛ ℓ h1).1⟩
  have hcard : (Λ'.card : ℝ) - A ≤ (Λ'.filter (A < ·)).card := by
    have h1 : Λ'.filter (fun ℓ => ¬ A < ℓ) ⊆ Finset.Icc 1 A := by
      intro ℓ hℓ
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hℓ
      have := cycleLengths_pos G (hΛ ℓ h1).1
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h2 := Finset.card_le_card h1
    rw [Nat.card_Icc] at h2
    have h3 := Finset.card_filter_add_card_filter_not (s := Λ') (fun ℓ => A < ℓ)
    have : Λ'.card ≤ (Λ'.filter (A < ·)).card + A := by omega
    have : (Λ'.card : ℝ) ≤ (Λ'.filter (A < ·)).card + A := by exact_mod_cast this
    linarith
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  calc ((Λ'.card : ℝ) - A) / M ≤ (Λ'.filter (A < ·)).card / M := by gcongr
    _ = ∑ ℓ ∈ Λ'.filter (A < ·), (1 : ℝ) / M := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ ℓ ∈ Λ'.filter (A < ·), (1 : ℝ) / ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have h1 := (hΛ ℓ (Finset.mem_filter.mp hℓ).1).2
        have h3 := cycleLengths_pos G (hΛ ℓ (Finset.mem_filter.mp hℓ).1).1
        apply one_div_le_one_div_of_le (by exact_mod_cast (show 0 < ℓ by omega))
        exact_mod_cast h1
    _ ≤ wAbove G A := by
        unfold wAbove
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

end T1main




section T1core

variable {V : Type} [Fintype V] {G : SimpleGraph V}

namespace HTree

lemma anc_eq_iter (T : HTree G) (ℓ : ℕ) (v : V) : T.anc ℓ v = T.par^[T.lev v - ℓ] v := rfl

/-- GKS Theorem 1 core: many distinct cycle lengths at scale `n`. -/
lemma T1_core (T : HTree G) (A : Finset V) (c : V → V × V) (hE : T.ValidExt A c)
    (n k : ℕ) (hn : 248 ≤ n) (hnh : n ≤ T.h) (hk1 : T.h - n ≤ k) (hk2 : k ≤ T.h)
    (ρ : V) (hρL : ρ ∈ T.L (T.h - n + 1))
    (hD1 : 2 ^ ((n - 1) / 4) ≤ (T.desc ρ (n - 1)).card)
    (hD2 : (T.desc ρ (n - 1)).card ≤
      32 * n ^ 2 * (n + 1) * ((T.desc ρ (n - 1)).filter (· ∈ T.Zs A c n k)).card) :
    ∃ Λ' : Finset ℕ, (∀ ℓ ∈ Λ', ℓ ∈ G.cycleLengths ∧ ℓ ≤ 4 * n + 4) ∧ n / 8 ≤ 3 * Λ'.card + 1 := by
  classical
  set Z := T.Zs A c n k with hZ
  set q := T.h - n + 1 with hq
  have hρT : ρ ∈ T.VT := (Finset.mem_filter.mp hρL).1
  have hρlev : T.lev ρ = q := (Finset.mem_filter.mp hρL).2
  have hZcρ : T.Zc Z ρ = ((T.desc ρ (n - 1)).filter (· ∈ Z)).card := by
    unfold Zc; rw [hρlev, show T.h - q = n - 1 by omega]
  have hZpos : 0 < T.Zc Z ρ := by
    rw [hZcρ]
    have : 1 ≤ 2 ^ ((n - 1) / 4) := Nat.one_le_two_pow
    by_contra h0; push Not at h0
    have : ((T.desc ρ (n - 1)).filter (· ∈ Z)).card = 0 := by omega
    rw [this] at hD2; omega
  have hpath := T.heavy_path Z ρ hρT hZpos
  have hHn : T.h - T.lev ρ = n - 1 := by omega
  obtain ⟨hpT, hplev, hppos, hpcount, _⟩ := hpath (n - 1) (by omega)
  set I := (Finset.range (n - 1)).filter (fun j => T.Br Z (T.hp Z ρ j)) with hI
  have hptop : T.hp Z ρ (n - 1) ∈ T.L T.h := Finset.mem_filter.mpr ⟨hpT, by omega⟩
  have hlast1 : T.Zc Z (T.hp Z ρ (n - 1)) ≤ 1 := by
    unfold Zc
    rw [show T.h - T.lev (T.hp Z ρ (n - 1)) = 0 by omega]
    exact le_trans (Finset.card_filter_le _ _) (by simpa using T.desc_card (T.hp Z ρ (n - 1)) 0)
  have ht : n / 8 ≤ I.card := by
    apply num2 n I.card hn
    calc 2 ^ ((n - 1) / 4) ≤ (T.desc ρ (n - 1)).card := hD1
      _ ≤ 32 * n ^ 2 * (n + 1) * T.Zc Z ρ := by rw [hZcρ]; exact hD2
      _ ≤ 32 * n ^ 2 * (n + 1) * (2 ^ I.card * T.Zc Z (T.hp Z ρ (n - 1))) := Nat.mul_le_mul_left _ hpcount
      _ ≤ 32 * n ^ 2 * (n + 1) * (2 ^ I.card * 1) := by gcongr
      _ = 2 ^ I.card * (32 * n ^ 2 * (n + 1)) := by ring
  -- the chosen Z-vertices
  have hheavy : ∀ i, T.heavy Z (T.hp Z ρ i) = T.hp Z ρ (i + 1) := by
    intro i; simp only [HTree.hp]; rw [Function.iterate_succ_apply']
  let Pz : ℕ → V → Prop := fun i z =>
    ∃ w ∈ T.ch (T.hp Z ρ i), w ≠ T.hp Z ρ (i + 1) ∧ z ∈ T.desc w (T.h - T.lev w) ∧ z ∈ Z
  let zf : ℕ → V := fun i => if h : ∃ z, Pz i z then Classical.choose h else T.hp Z ρ (n - 1)
  have hzI : ∀ i ∈ I, Pz i (zf i) := by
    intro i hi
    obtain ⟨_, w, hw, hwne, hwpos⟩ := Finset.mem_filter.mp hi
    have hex : ∃ z, Pz i z := by
      unfold Zc at hwpos
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hwpos
      exact ⟨z, w, hw, by rw [← hheavy]; exact hwne, (Finset.mem_filter.mp hz).1,
        (Finset.mem_filter.mp hz).2⟩
    simp only [zf, dif_pos hex]; exact Classical.choose_spec hex
  have hzlast : zf (n - 1) = T.hp Z ρ (n - 1) := by
    simp only [zf]
    rw [dif_neg]
    rintro ⟨z, w, hw, _⟩
    rw [T.top_no_child _ hptop] at hw
    simp at hw
  have hIlt : ∀ i ∈ I, i < n - 1 := fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  -- properties of the chosen vertices
  have hzprop : ∀ i, (i ∈ I ∨ i = n - 1) → zf i ∈ Z ∧ zf i ∈ T.VT ∧ T.lev (zf i) = T.h ∧
      ∀ j, j ≤ i → T.anc (q + j) (zf i) = T.hp Z ρ j := by
    intro i hi
    rcases hi with hi | hi
    · obtain ⟨w, hw, _, hzd, hzZ⟩ := hzI i hi
      have hil := hIlt i hi
      obtain ⟨hpiT, hpil, _, _, hpianc⟩ := hpath i (by omega)
      obtain ⟨hlw, haw⟩ := T.anc_of_ch hw
      simp only [desc, Finset.mem_filter] at hzd
      obtain ⟨hzT, hzl, hza⟩ := hzd
      have hwl : T.lev w ≤ T.h := T.lev_le w (T.ch_mem hw)
      refine ⟨hzZ, hzT, by omega, fun j hj => ?_⟩
      calc T.anc (q + j) (zf i) = T.anc (q + j) (T.anc (T.lev w) (zf i)) :=
            (T.anc_anc _ _ _ (by omega) (by omega)).symm
        _ = T.anc (q + j) w := by rw [hza]
        _ = T.anc (q + j) (T.anc (T.lev (T.hp Z ρ i)) w) := (T.anc_anc _ _ _ (by omega) (by omega)).symm
        _ = T.anc (q + j) (T.hp Z ρ i) := by rw [haw]
        _ = T.hp Z ρ j := by rw [← hρlev]; exact hpianc j hj
    · subst hi
      rw [hzlast]
      obtain ⟨hT', hl', hpos', _, hanc'⟩ := hpath (n - 1) (by omega)
      refine ⟨T.Zc_top Z _ (by omega) hT' hpos', hT', by omega, fun j hj => ?_⟩
      rw [← hρlev]; exact hanc' j hj
  have hzoff : ∀ i ∈ I, T.anc (q + i + 1) (zf i) ≠ T.hp Z ρ (i + 1) := by
    intro i hi
    obtain ⟨w, hw, hwne, hzd, _⟩ := hzI i hi
    have hil := hIlt i hi
    obtain ⟨_, hpil, _, _, _⟩ := hpath i (by omega)
    obtain ⟨hlw, _⟩ := T.anc_of_ch hw
    simp only [desc, Finset.mem_filter] at hzd
    rw [show q + i + 1 = T.lev w by omega, hzd.2.2]
    exact hwne
  -- facts about the chosen vertices
  have hI' : ∀ i ∈ I, i + 1 < n := fun i hi => by have := hIlt i hi; omega
  have hlast : (n - 1 ∈ I ∨ n - 1 = n - 1) := Or.inr rfl
  have hroot : ∀ i, (i ∈ I ∨ i = n - 1) → T.anc q (zf i) = ρ := by
    intro i hi
    have := (hzprop i hi).2.2.2 0 (Nat.zero_le _)
    rw [add_zero] at this; rw [this]; rfl
  have hSCzz : ∀ i j, (i ∈ I ∨ i = n - 1) → (j ∈ I ∨ j = n - 1) → T.SC (n - 1) (zf i) (zf j) := by
    intro i j hi hj
    refine ⟨by rw [(hzprop i hi).2.2.1]; omega, by rw [(hzprop j hj).2.2.1]; omega, ?_⟩
    rw [show T.h - (n - 1) = q by omega, hroot i hi, hroot j hj]
  have hSCzzn : ∀ i j, (i ∈ I ∨ i = n - 1) → (j ∈ I ∨ j = n - 1) → T.SC n (zf i) (zf j) :=
    fun i j hi hj => SC.mono T (by omega) (hSCzz i j hi hj)
  -- the target relation
  let R : V → V → Prop := fun x t =>
    t ∈ T.VT ∧ T.Join A c x t ∧ T.SC n x t ∧ ¬ T.SC (n - 1) x t ∧ T.lev t = k
  let JV := JVc (T.CG A c) (Ys A c)
  let β := fβ T.par n
  have hJV : ∀ x t, T.Join A c x t → ∃ cen, JV x t cen := by
    intro x t h
    rcases h with h | ⟨y, hy, h1, h2⟩
    · exact ⟨none, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨some y, Or.inr ⟨y, rfl, hy, h1, h2⟩⟩
  -- the tree path of a vertex `zf i` stays under `ρ`
  have hunder : ∀ i, (i ∈ I ∨ i = n - 1) → ∀ s, s ≤ n - 1 →
      q ≤ T.lev (T.par^[s] (zf i)) ∧ T.anc q (T.par^[s] (zf i)) = ρ ∧ T.par^[s] (zf i) ∈ T.VT := by
    intro i hi s hs
    obtain ⟨_, hzT, hzl, _⟩ := hzprop i hi
    have hl := lev_iter T.isParent s (zf i) (by omega)
    refine ⟨by omega, ?_, T.iter_mem _ hzT s (by omega)⟩
    have e : T.par^[s] (zf i) = T.anc (T.lev (zf i) - s) (zf i) := by
      rw [anc_eq_iter]; congr 1; omega
    rw [e, T.anc_anc _ _ _ (by omega) (by omega), hroot i hi]
  -- targets' tree paths avoid `ρ`'s cone
  have hout : ∀ i, (i ∈ I ∨ i = n - 1) → ∀ t, R (zf i) t → ∀ s, s ≤ T.lev t →
      ¬ (q ≤ T.lev (T.par^[s] t) ∧ T.anc q (T.par^[s] t) = ρ) ∧ T.par^[s] t ∈ T.VT := by
    intro i hi t ht s hs
    obtain ⟨htT, _, _, hnsc, htl⟩ := ht
    refine ⟨?_, T.iter_mem _ htT s hs⟩
    rintro ⟨h1, h2⟩
    have hl := lev_iter T.isParent s t hs
    have e : T.par^[s] t = T.anc (T.lev t - s) t := by rw [anc_eq_iter]; congr 1; omega
    rw [e, T.anc_anc _ _ _ (by omega) (by omega)] at h2
    apply hnsc
    refine ⟨by rw [(hzprop i hi).2.2.1]; omega, by omega, ?_⟩
    rw [show T.h - (n - 1) = q by omega, hroot i hi, h2]
  -- common iterate of two targets
  have hcommon : ∀ i j, (i ∈ I ∨ i = n - 1) → (j ∈ I ∨ j = n - 1) → ∀ a b, R (zf i) a → R (zf j) b →
      T.par^[k - (T.h - n)] b = T.par^[k - (T.h - n)] a := by
    intro i j hi hj a b ha hb
    have e1 : T.anc (T.h - n) a = T.anc (T.h - n) (zf i) := (ha.2.2.1).2.2.symm
    have e2 : T.anc (T.h - n) b = T.anc (T.h - n) (zf j) := (hb.2.2.1).2.2.symm
    have e3 := (hSCzzn i j hi hj).2.2
    rw [anc_eq_iter, anc_eq_iter, ha.2.2.2.2] at e1
    rw [anc_eq_iter, hb.2.2.2.2] at e2
    rw [e1, e2] at *
    exact e3.symm.trans e3 |>.symm ▸ (by rw [e2, e1]; exact e3.symm)
  have hP := T.isParent
  have hpa : ∀ v, T.lev v = T.h → ∀ ℓ, ℓ ≤ T.h → T.par^[T.h - ℓ] v = T.anc ℓ v := by
    intro v hv ℓ _; rw [anc_eq_iter, hv]
  have hYV : ∀ y ∈ Ys A c, ∀ x ∈ T.VT, y ≠ x := fun y hy x hx e => T.Ys_disj A c hE y hy (e ▸ hx)
  have hquad : ∀ i ∈ I, ∀ j, (j ∈ I ∨ j = n - 1) → i < j → ∀ a b c1 c2, R (zf i) a → R (zf j) b →
      JV (zf i) a c1 → JV (zf j) b c2 → (∀ y, c1 = some y → c2 ≠ some y) →
      2 * (n - 1 - i) + 2 * β a b + 2 + (optL c1).length + (optL c2).length ∈ G.cycleLengths := by
    intro i hi j hj hij a b c1 c2 ha hb hJa hJb hcen
    have hil := hIlt i hi
    have hjl : j ≤ n - 1 := by
      rcases hj with hj | hj
      · have := hIlt j hj; omega
      · omega
    obtain ⟨_, hziT, hzil, hzia⟩ := hzprop i (Or.inl hi)
    obtain ⟨_, hzjT, hzjl, hzja⟩ := hzprop j hj
    have hs0 := hcommon i j (Or.inl hi) hj a b ha hb
    obtain ⟨hβle', hβeq, hβne⟩ := fβ_spec T.par n b a (k - (T.h - n)) (by omega) hs0
    have eβ : fβ T.par n b a = fβ T.par n a b := fβ_symm _ _ _ _
    rw [eβ] at hβle' hβeq hβne
    have hβ1 : β a b ≤ k - (T.h - n) := hβle'
    have hz1 : T.anc (q + i + 1) (zf j) = T.hp Z ρ (i + 1) := hzja (i + 1) (by omega)
    have hbl : T.lev b = k := hb.2.2.2.2
    have hal : T.lev a = k := ha.2.2.2.2
    have e1 : T.par^[n - 1 - i] (zf i) = T.anc (q + i) (zf i) := by
      rw [← hpa _ hzil _ (by omega)]; congr 1; omega
    have e2 : T.par^[n - 1 - i] (zf j) = T.anc (q + i) (zf j) := by
      rw [← hpa _ hzjl _ (by omega)]; congr 1; omega
    have e3 : T.par^[n - 1 - i - 1] (zf i) = T.anc (q + i + 1) (zf i) := by
      rw [← hpa _ hzil _ (by omega)]; congr 1; omega
    have e4 : T.par^[n - 1 - i - 1] (zf j) = T.anc (q + i + 1) (zf j) := by
      rw [← hpa _ hzjl _ (by omega)]; congr 1; omega
    refine quad_cycle hP (zf i) (zf j) a b (n - 1 - i) (β a b) (by omega) (by omega)
      (by rw [hzil, hzjl]) (by rw [e1, e2, hzia i le_rfl, hzja i (by omega)])
      (by rw [e3, e4, hz1]; exact hzoff i hi)
      (by rw [hbl]; omega) (by rw [hal, hbl]) hβeq hβne c1 c2 ?_ ?_ ?_ ?_ hcen ?_ ?_ ?_
    · intro y hy; subst hy
      obtain ⟨_, h1, h2⟩ := JVc_some hJb
      exact ⟨h1.1, h2.1⟩
    · intro h; subst h; exact (JVc_none hJb).1
    · intro y hy; subst hy
      obtain ⟨_, h1, h2⟩ := JVc_some hJa
      exact ⟨h2.1.symm, h1.1.symm⟩
    · intro h; subst h; exact (JVc_none hJa).1.symm
    · intro i' hi' j' hj'
      obtain ⟨u1, u2, _⟩ := hunder i (Or.inl hi) i' (by omega)
      obtain ⟨u1', u2', _⟩ := hunder j hj i' (by omega)
      obtain ⟨o1, _⟩ := hout i (Or.inl hi) a ha j' (by omega)
      obtain ⟨o2, _⟩ := hout j hj b hb j' (by omega)
      refine ⟨fun e => o2 ?_, fun e => o1 ?_, fun e => o2 ?_, fun e => o1 ?_⟩
      · rw [← e]; exact ⟨u1, u2⟩
      · rw [← e]; exact ⟨u1, u2⟩
      · rw [← e]; exact ⟨u1', u2'⟩
      · rw [← e]; exact ⟨u1', u2'⟩
    · intro y hy i' hi'
      have hyY : y ∈ Ys A c := by
        rcases hy with h | h
        · rw [h] at hJa; exact (JVc_some hJa).1
        · rw [h] at hJb; exact (JVc_some hJb).1
      exact ⟨hYV y hyY _ (hunder i (Or.inl hi) i' (by omega)).2.2,
        hYV y hyY _ (hunder j hj i' (by omega)).2.2⟩
    · intro y hy j' hj'
      have hyY : y ∈ Ys A c := by
        rcases hy with h | h
        · rw [h] at hJa; exact (JVc_some hJa).1
        · rw [h] at hJb; exact (JVc_some hJb).1
      exact ⟨hYV y hyY _ (hout j hj b hb j' (by omega)).2, hYV y hyY _ (hout i (Or.inl hi) a ha j' (by omega)).2⟩
  have hc2 : ∀ j ∈ I, ∀ v a b, R (zf j) a → JV (zf j) a (some v) → R (zf (n - 1)) b →
      JV (zf (n - 1)) b (some v) → 2 * (n - 1 - j) + 2 ∈ G.cycleLengths := by
    intro j hj v a b _ hJa _ hJb
    have hjl := hIlt j hj
    obtain ⟨_, hzjT, hzjl, hzja⟩ := hzprop j (Or.inl hj)
    obtain ⟨_, hzlT, hzll, hzla⟩ := hzprop (n - 1) (Or.inr rfl)
    obtain ⟨hvY, ha1, _⟩ := JVc_some hJa
    obtain ⟨_, hb1, _⟩ := JVc_some hJb
    have hz1 : T.anc (q + j + 1) (zf (n - 1)) = T.hp Z ρ (j + 1) := hzla (j + 1) (by omega)
    have e1 : T.par^[n - 1 - j] (zf j) = T.anc (q + j) (zf j) := by
      rw [← hpa _ hzjl _ (by omega)]; congr 1; omega
    have e2 : T.par^[n - 1 - j] (zf (n - 1)) = T.anc (q + j) (zf (n - 1)) := by
      rw [← hpa _ hzll _ (by omega)]; congr 1; omega
    have e3 : T.par^[n - 1 - j - 1] (zf j) = T.anc (q + j + 1) (zf j) := by
      rw [← hpa _ hzjl _ (by omega)]; congr 1; omega
    have e4 : T.par^[n - 1 - j - 1] (zf (n - 1)) = T.anc (q + j + 1) (zf (n - 1)) := by
      rw [← hpa _ hzll _ (by omega)]; congr 1; omega
    have key := tree_list_cycle hP (zf j) (zf (n - 1)) (n - 1 - j) (by omega) (by omega)
      (by rw [hzjl, hzll]) (by rw [e1, e2, hzja j le_rfl, hzla j (by omega)])
      (by rw [e3, e4, hz1]; exact hzoff j hj) [v] (List.cons_ne_nil _ _)
      (List.nodup_singleton _) (List.isChain_singleton _) ?_ hb1.1 ha1.1.symm
    · simpa using key
    · intro x hx i' hi'
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨hYV _ hvY _ (hunder j (Or.inl hj) i' (by omega)).2.2,
        hYV _ hvY _ (hunder (n - 1) (Or.inr rfl) i' (by omega)).2.2⟩
  have hreroute : ∀ i ∈ I, ∀ κ, (κ ∈ I ∨ κ = n - 1) → i < κ → ∀ a x y, R (zf i) a →
      JV (zf i) a (some y) → R (zf κ) x → JV (zf κ) x (some y) → R (zf i) x ∧ JV (zf i) x (some y) := by
    intro i hi κ hκ _ a x y _ hJa hx hJx
    obtain ⟨hy, h1, _⟩ := JVc_some hJa
    obtain ⟨_, _, h2⟩ := JVc_some hJx
    have hsc := hSCzzn i κ (Or.inl hi) hκ
    have hsc' := hSCzz i κ (Or.inl hi) hκ
    exact ⟨⟨hx.1, Or.inr ⟨y, hy, h1, h2⟩, SC.trans T hsc hx.2.2.1,
      fun h => hx.2.2.2.1 (SC.trans T (SC.symm T hsc') h), hx.2.2.2.2⟩, Or.inr ⟨y, rfl, hy, h1, h2⟩⟩
  have hne : ∀ i, (i ∈ I ∨ i = n - 1) → ∃ t cen, R (zf i) t ∧ JV (zf i) t cen := by
    intro i hi
    have hzZ := (hzprop i hi).1
    simp only [hZ, HTree.Zs, Finset.mem_filter] at hzZ
    obtain ⟨_, t, ht, hj, hsc, hnsc, hl⟩ := hzZ
    obtain ⟨cen, hc⟩ := hJV _ _ hj
    exact ⟨t, cen, ⟨ht, hj, hsc, hnsc, hl⟩, hc⟩
  obtain ⟨Λ', h1, h2⟩ := count_core n I hI' zf R JV β (fβ_symm T.par n) (fβ_ultra T.par n) (fβ_le T.par n)
    G.cycleLengths hquad hc2 hreroute hne
  exact ⟨Λ', h1, by omega⟩

end HTree

end T1core

section T1holds

/-- GKS Theorem 1 (Corollary 1). -/
lemma T1_holds : T1stmt := by
  refine ⟨144 * 2 ^ 2000, 144, by norm_num, 1 / 500, by norm_num, ?_⟩
  intro V _ G S d hSne hd hdeg hsupp P hP
  classical
  obtain ⟨r, hr⟩ := hSne
  have hd144 : 2 ^ 2000 ≤ d / 144 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  set P' := max P (d / 144) with hP'def
  have hP' : ∀ F T', F ≤ G → DensePair F T' ((d : ℝ) / 144) → P' ≤ LP F := by
    intro F T' hF hD
    apply max_le (hP F T' hF hD)
    have hpos : (0 : ℝ) < (d : ℝ) / 144 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by have := Nat.one_le_two_pow (n := 2000); omega)
      positivity
    have h1 := LP_ge F T' _ hpos hD
    have h2 : ((d / 144 : ℕ) : ℝ) ≤ (d : ℝ) / 144 := by
      have := Nat.cast_div_le (α := ℝ) (m := d) (n := 144)
      simpa using this
    exact_mod_cast le_trans h2 h1
  have hP'ge : 2 ^ 2000 ≤ P' := le_trans hd144 (le_max_right _ _)
  have hP'ne : P' ≠ 0 := by have := Nat.one_le_two_pow (n := 2000); omega
  set L := Nat.log 2 P' with hLdef
  have hL : 2000 ≤ L := Nat.le_log_of_pow_le (by norm_num) hP'ge
  have hLP : 2 ^ L ≤ P' := Nat.pow_log_le_self 2 hP'ne
  have hmono : wAbove G (L / 64) ≤ wAbove G (Nat.log 2 P / 64) :=
    wAbove_anti G (Nat.div_le_div_right (Nat.log_mono_right (le_max_left _ _)))
  refine le_trans ?_ hmono
  set m := L - 2 with hm
  have hm2 : 2 ^ (m + 2) ≤ P' := by rw [show m + 2 = L by omega]; exact hLP
  obtain ⟨T, hTr, A, c, hE, hA, hBprop⟩ := HTree.exists_setup (G := G) r
  have hroot : T.root ∈ S := hTr ▸ hr
  have hd4 : 4 ≤ d := by have := Nat.one_le_two_pow (n := 2000); omega
  have hc1 := T.claim1 A c S d hsupp hroot hdeg hd4 hE hA hBprop P' hP' m hm2
  set Far := (T.Bc A).filter (fun x => ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t) with hFar
  obtain ⟨hB4, _⟩ := T.Bc_card A c hA hE.1
  have hLpos := (T.L_nonempty T.h le_rfl).card_pos
  have hFne : Far.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hFar' : ∀ x ∈ Far, x ∈ T.Bc A ∧ ∃ t ∈ T.VT, T.Join A c x t ∧ ¬ T.SC m x t :=
    fun x hx => Finset.mem_filter.mp hx
  obtain ⟨n, k, hmn, hnh, hk1, hk2, hcnt⟩ := T.claim2 A c m (by omega) Far hFar' hFne
  set Z := T.Zs A c n k with hZ
  have hZsub : Z ⊆ T.L T.h := fun x hx =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
  obtain ⟨W, hW⟩ : ∃ W, W = n ^ 2 * (n + 1) * Z.card := ⟨_, rfl⟩
  have e1 : 2 * n ^ 2 * (n + 1) * Z.card = 2 * W := by rw [hW]; ring
  have e2 : 16 * n ^ 2 * (n + 1) * Z.card = 16 * W := by rw [hW]; ring
  have hbig : (T.L T.h).card < 16 * n ^ 2 * (n + 1) * Z.card := by
    rw [e1] at hcnt; rw [e2]; omega
  obtain ⟨ρ, hρL, hD1, hD2⟩ := T.claim3 Z n (by omega) hnh hZsub hbig
  obtain ⟨Λ', hΛ', hcard⟩ := T.T1_core A c hE n k (by omega) hnh hk1 hk2 ρ hρL hD1 hD2
  have hw := weight_of_set G Λ' (4 * n + 4) (L / 64) (by omega) hΛ'
  refine le_trans ?_ hw
  have hnat : 4 * n + 4 + 500 * (L / 64) ≤ 500 * Λ'.card := by omega
  have hr' : ((4 * n + 4 : ℕ) : ℝ) + 500 * ((L / 64 : ℕ) : ℝ) ≤ 500 * (Λ'.card : ℝ) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < ((4 * n + 4 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  linarith

end T1holds

end OMA65

end

theorem OMA.solution : type_of% @Erdos65.erdos_65.parts.i :=
  OMA65.main_of_MGT (OMA65.MGT_of_ML (OMA65.ML_of_T1 OMA65.T1_holds))
