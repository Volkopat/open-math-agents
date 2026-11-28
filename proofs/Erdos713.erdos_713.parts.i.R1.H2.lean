import OMAReductions.R_Erdos713_erdos_713_parts_i_R1

/-!
Elementary proof of `Erdos713.erdos_713.parts.i.R1.H2`:
If a finite graph `H` with no isolated vertices and a vertex of degree at least 2 satisfies
`extremalNumber n H = O(n)`, then `extremalNumber n H ~ c * n` for some `c > 0`.

Proof overview (completely self-contained):
1. By `tendsto_of_no_upcrossings` over `ℚ`, existence of `lim ex(n, H) / n` reduces to showing
   that for any `0 < a < b`, if `ex(n, H) > b * n` infinitely often then `ex(m, H) ≥ a * m`
   for all sufficiently large `m`.
2. Given `0 < a < b` and `ε = (b - a) / 2`, define a rapidly decreasing rational degree-threshold
   sequence `δ_0 > δ_1 > ... > δ_L > 0` where `2C / L ≤ ε / 4` and `δ_{k+1}` is tiny relative to
   the number of attachment patterns on a set `S` of size `≤ 2C / δ_k`.
3. For a large `H`-free extremal host `G` on `n` vertices with `b * n < e(G) ≤ C * n`, pigeonhole
   gives an index `k < L` whose degree shell `A_k = {v : δ_{k+1} n ≤ deg v < δ_k n}` has total
   degree `≤ (ε / 4) n`. Put `S = {v : deg v ≥ δ_k n}` and `R = {v : deg v < δ_{k+1} n}`.
4. Clean `R` to `R' ⊆ R` by strong induction on the number of realizable attachment patterns
   `(comp, attach)` relative to `S`: any pattern with fewer than `q` pairwise vertex-disjoint
   realizations is eliminated by removing a maximal packing (`≤ q^2` vertices).
5. Form the apex-blowup `G'^{(t)}(S)` (one copy of `S`, `t` disjoint copies of `R'` joined to `S`
   as in `G`, plus `r` isolated vertices). Any copy of `H` in `G'^{(t)}(S)` avoids the isolated
   vertices, maps each connected component of `H \ φ⁻¹(S)` into a single copy of `R'`, and by
   cleaning each such pattern has `≥ q` pairwise disjoint realizations in `R'`, allowing greedy
   vertex-disjoint re-embedding into `G`, contradicting `H.Free G`.
6. Edge counting yields `e(G'^{(t)}(S)) ≥ t * E_good ≥ (a + 5ε/4) * (m - n) ≥ a * m` for all
   sufficiently large `m`, establishing convergence; a matching host gives limit `≥ 1/2 > 0`.
-/

namespace E713H2Proof

open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology

section DensityFramework

private theorem even_lower {q : ℕ} (H : SimpleGraph (Fin q)) (branch : ∃ v, 2 ≤ H.degree v) (k : ℕ) :
    k ≤ extremalNumber (2 * k) H := by
  let V := Fin k × Bool
  let X : SimpleGraph V := {
    Adj := fun a b => a.1 = b.1 ∧ a.2 ≠ b.2
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }
  have singleton (u : V) : X.neighborFinset u = {(u.1, !u.2)} := by
    ext v
    rcases u with ⟨i, b⟩
    rcases v with ⟨j, c⟩
    cases b <;> cases c <;> simp [V, X, mem_neighborFinset, Prod.mk.injEq, eq_comm]
  have deg (u : V) : X.degree u = 1 := by
    rw [← card_neighborFinset_eq_degree, singleton, card_singleton]
  have free : H.Free X := by
    rintro ⟨f⟩
    obtain ⟨v, hv⟩ := branch
    have lim := f.degree_le v
    rw [deg] at lim
    omega
  have sum := X.sum_degrees_eq_twice_card_edges
  simp only [deg, sum_const, card_univ, smul_eq_mul, mul_one] at sum
  have card : Fintype.card V = 2 * k := by simp [V, Nat.mul_comm]
  have e := card_edgeFinset_le_extremalNumber free
  rw [card] at e sum
  omega

private theorem positive_limit {q : ℕ} (H : SimpleGraph (Fin q)) (branch : ∃ v, 2 ≤ H.degree v)
    (c : ℝ) (lim : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop (𝓝 c)) :
    0 < c ∧ IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ)) (fun n => c * n) := by
  have even : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b, fun k hk => by omega⟩)
  have half : (1 : ℝ) / 2 ≤ c := by
    apply ge_of_tendsto (lim.comp even)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    change (1 : ℝ) / 2 ≤ (extremalNumber (2 * k) H : ℝ) / (2 * k : ℕ)
    have low : (k : ℝ) ≤ extremalNumber (2 * k) H := by exact_mod_cast even_lower H branch k
    push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have pos : 0 < c := by linarith
  refine ⟨pos, isEquivalent_of_tendsto_one ?_⟩
  have L := lim.div_const c
  rw [div_self pos.ne'] at L
  apply L.congr'
  filter_upwards with n
  change (extremalNumber n H : ℝ) / n / c = (extremalNumber n H : ℝ) / (c * n)
  rw [div_div, mul_comm]

private theorem sustained {q : ℕ} (H : SimpleGraph (Fin q)) (C : ℕ)
    (cap : ∀ᶠ n : ℕ in atTop, extremalNumber n H ≤ C * n)
    (transfer : ∀ a b : ℚ, 0 < a → a < b →
      (∀ N, ∃ n ≥ N, b * n < (extremalNumber n H : ℚ)) →
      ∃ M, ∀ m ≥ M, a * m ≤ (extremalNumber m H : ℚ)) :
    ∃ c : ℝ, Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop (𝓝 c) := by
  let u (n : ℕ) := (extremalNumber n H : ℝ) / n
  have above : atTop.IsBoundedUnder (· ≤ ·) u := by
    refine ⟨(C : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, u n ≤ (C : ℝ)
    filter_upwards [cap, eventually_gt_atTop (0 : ℕ)] with n hn pos
    change (extremalNumber n H : ℝ) / n ≤ C
    exact (div_le_iff₀ (by positivity)).mpr (by exact_mod_cast hn)
  have below : atTop.IsBoundedUnder (· ≥ ·) u := by
    refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ u n
    exact Eventually.of_forall (fun n => by dsimp [u]; positivity)
  apply tendsto_of_no_upcrossings (s := Set.range ((↑) : ℚ → ℝ)) Rat.denseRange_cast _ above below
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ ab ⟨down, up⟩
  have hab : a < b := by exact_mod_cast ab
  have hM : ∃ M, ∀ m ≥ M, a * m ≤ (extremalNumber m H : ℚ) := by
    by_cases ha : 0 < a
    · apply transfer a b ha hab
      intro N
      obtain ⟨n, hn, high⟩ := frequently_atTop.mp up (N + 1)
      have pos : 0 < n := by omega
      have high' := (lt_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast pos)).mp high
      exact ⟨n, by omega, by exact_mod_cast high'⟩
    · refine ⟨0, fun m _ => ?_⟩
      have ha' : a ≤ 0 := not_lt.mp ha
      have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      have h1 : a * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha' hm
      exact h1.trans (Nat.cast_nonneg _)
  obtain ⟨M, hM⟩ := hM
  obtain ⟨n, hn, dip⟩ := frequently_atTop.mp down (M + 1)
  have pos : 0 < n := by omega
  have dip' := (div_lt_iff₀ (show (0 : ℝ) < n by exact_mod_cast pos)).mp dip
  have low := hM n (by omega)
  have low' : (a : ℝ) * n ≤ extremalNumber n H := by exact_mod_cast low
  exact (not_lt_of_ge low') dip'

end DensityFramework

section PatternCleaning

abbrev Pattern (q : ℕ) (S : Type*) := Finset (Fin q) × (Fin q → Option S)

private theorem card_pattern (q : ℕ) {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (Pattern q S) = 2 ^ q * (S.card + 1) ^ q := by
  simp [Pattern, Fintype.card_prod, Fintype.card_pi, Fintype.card_option, Fintype.card_fin]

def IsRealization {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) (p : Pattern q S) (f : Fin q → Fin n) : Prop :=
  (∀ u ∈ p.1, f u ∈ R) ∧
  Set.InjOn f (p.1 : Set (Fin q)) ∧
  (∀ u ∈ p.1, ∀ v ∈ p.1, H.Adj u v → G.Adj (f u) (f v)) ∧
  (∀ u ∈ p.1, ∀ a : Fin q, ∀ s : S, p.2 a = some s → H.Adj u a → G.Adj (f u) s.1)

def HasRealization {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) (p : Pattern q S) : Prop :=
  ∃ f : Fin q → Fin n, IsRealization H G S R p f

def HasDisjoint {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) (p : Pattern q S) (m : ℕ) : Prop :=
  ∃ F : Fin m → (Fin q → Fin n),
    (∀ i, IsRealization H G S R p (F i)) ∧
    (∀ i j, i ≠ j → ∀ u ∈ p.1, ∀ v ∈ p.1, F i u ≠ F j v)

private theorem isRealization_mono {q n : ℕ} {H : SimpleGraph (Fin q)} {G : SimpleGraph (Fin n)}
    {S R₁ R₂ : Finset (Fin n)} {p : Pattern q S} {f : Fin q → Fin n}
    (hsub : R₁ ⊆ R₂) (hf : IsRealization H G S R₁ p f) : IsRealization H G S R₂ p f :=
  ⟨fun u hu => hsub (hf.1 u hu), hf.2.1, hf.2.2.1, hf.2.2.2⟩

private theorem hasRealization_mono {q n : ℕ} {H : SimpleGraph (Fin q)} {G : SimpleGraph (Fin n)}
    {S R₁ R₂ : Finset (Fin n)} {p : Pattern q S}
    (hsub : R₁ ⊆ R₂) (h : HasRealization H G S R₁ p) : HasRealization H G S R₂ p :=
  let ⟨f, hf⟩ := h; ⟨f, isRealization_mono hsub hf⟩

private theorem kill_pattern {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) (p : Pattern q S) (hnot : ¬ HasDisjoint H G S R p q) :
    ∃ U : Finset (Fin n), U ⊆ R ∧ U.card ≤ q * q ∧ ¬ HasRealization H G S (R \ U) p := by
  let T : Finset ℕ := (Finset.range (q + 1)).filter (fun m => HasDisjoint H G S R p m)
  have h0 : 0 ∈ T := by
    rw [mem_filter, mem_range]
    exact ⟨Nat.succ_pos q, ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  have hTne : T.Nonempty := ⟨0, h0⟩
  let m₀ := T.max' hTne
  have hm₀_mem : m₀ ∈ T := max'_mem T hTne
  rw [mem_filter, mem_range] at hm₀_mem
  have hm₀_lt : m₀ < q := by
    by_contra! hge
    have heq : m₀ = q := by omega
    have hdisj_m₀ := hm₀_mem.2
    rw [heq] at hdisj_m₀
    exact hnot hdisj_m₀
  obtain ⟨F, hF, hdisj⟩ := hm₀_mem.2
  let U : Finset (Fin n) := (univ : Finset (Fin m₀)).biUnion (fun i => p.1.image (F i))
  refine ⟨U, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx'
    exact (hF i).1 u hu
  · calc
      U.card ≤ ∑ i : Fin m₀, (p.1.image (F i)).card := card_biUnion_le
      _ ≤ ∑ _i : Fin m₀, q := by
        refine sum_le_sum fun i _ => ?_
        calc (p.1.image (F i)).card ≤ p.1.card := card_image_le
          _ ≤ Fintype.card (Fin q) := card_le_univ p.1
          _ = q := Fintype.card_fin q
      _ = m₀ * q := by simp
      _ ≤ q * q := Nat.mul_le_mul_right q hm₀_lt.le
  · rintro ⟨g, hg⟩
    let F' : Fin (m₀ + 1) → (Fin q → Fin n) :=
      fun i => if h : i.1 < m₀ then F ⟨i.1, h⟩ else g
    have hF' : HasDisjoint H G S R p (m₀ + 1) := by
      refine ⟨F', ?_, ?_⟩
      · intro i
        dsimp [F']
        split_ifs with h
        · exact hF ⟨i.1, h⟩
        · exact isRealization_mono sdiff_subset hg
      · intro i j hij u hu v hv eq
        by_cases hi : i.1 < m₀ <;> by_cases hj : j.1 < m₀
        · simp only [F', dif_pos hi, dif_pos hj] at eq
          apply hdisj ⟨i.1, hi⟩ ⟨j.1, hj⟩ _ u hu v hv eq
          intro hsub
          apply hij
          exact Fin.ext (by simpa using congrArg Fin.val hsub)
        · simp only [F', dif_pos hi, dif_neg hj] at eq
          have hmem : F ⟨i.1, hi⟩ u ∈ U :=
            mem_biUnion.mpr ⟨⟨i.1, hi⟩, mem_univ _, mem_image.mpr ⟨u, hu, rfl⟩⟩
          rw [eq] at hmem
          exact (mem_sdiff.mp (hg.1 v hv)).2 hmem
        · simp only [F', dif_neg hi, dif_pos hj] at eq
          have hmem : F ⟨j.1, hj⟩ v ∈ U :=
            mem_biUnion.mpr ⟨⟨j.1, hj⟩, mem_univ _, mem_image.mpr ⟨v, hv, rfl⟩⟩
          rw [← eq] at hmem
          exact (mem_sdiff.mp (hg.1 u hu)).2 hmem
        · apply hij
          exact Fin.ext (by omega)
    have hmem' : m₀ + 1 ∈ T := by
      rw [mem_filter, mem_range]
      exact ⟨by omega, hF'⟩
    have hle : m₀ + 1 ≤ m₀ := le_max' T (m₀ + 1) hmem'
    omega

private noncomputable def liveSet {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) : Finset (Pattern q S) :=
  (univ : Finset (Pattern q S)).filter (fun p => HasRealization H G S R p)

private theorem clean_all_aux {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (k : ℕ) :
    ∀ R : Finset (Fin n), (liveSet H G S R).card ≤ k →
      ∃ R' ⊆ R, (R \ R').card ≤ k * (q * q) ∧
        ∀ p : Pattern q S, HasRealization H G S R' p → HasDisjoint H G S R' p q := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro R hk
    by_cases hall : ∀ p : Pattern q S, HasRealization H G S R p → HasDisjoint H G S R p q
    · exact ⟨R, Subset.rfl, by simp, hall⟩
    · push Not at hall
      obtain ⟨p₀, hp₀_real, hp₀_not⟩ := hall
      have hpos : 0 < (liveSet H G S R).card :=
        card_pos.mpr ⟨p₀, mem_filter.mpr ⟨mem_univ _, hp₀_real⟩⟩
      obtain ⟨U, hUR, hUcard, hp₀_dead⟩ := kill_pattern H G S R p₀ hp₀_not
      let R₁ := R \ U
      have hsub : liveSet H G S R₁ ⊂ liveSet H G S R := by
        rw [ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [liveSet, mem_filter] at hp ⊢
          exact ⟨mem_univ _, hasRealization_mono sdiff_subset hp.2⟩
        · intro heq
          have : p₀ ∈ liveSet H G S R₁ := by
            rw [heq, liveSet, mem_filter]
            exact ⟨mem_univ _, hp₀_real⟩
          exact hp₀_dead (mem_filter.mp this).2
      have hlt : (liveSet H G S R₁).card < (liveSet H G S R).card := card_lt_card hsub
      obtain ⟨R', hR'R₁, hR'card, hR'clean⟩ := ih (k - 1) (by omega) R₁ (by omega)
      refine ⟨R', hR'R₁.trans sdiff_subset, ?_, hR'clean⟩
      have hcov : R \ R' ⊆ U ∪ (R₁ \ R') := by
        intro x hx
        obtain ⟨hxR, hxR'⟩ := mem_sdiff.mp hx
        by_cases hxU : x ∈ U
        · exact mem_union_left _ hxU
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxR, hxU⟩, hxR'⟩)
      have hle := (card_le_card hcov).trans (card_union_le U (R₁ \ R'))
      have hmul : q * q + (k - 1) * (q * q) = k * (q * q) := by
        cases k with
        | zero => omega
        | succ m => simp [Nat.succ_mul, Nat.add_comm]
      omega

private theorem clean_all {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R : Finset (Fin n)) :
    ∃ R' ⊆ R, (R \ R').card ≤ 2 ^ q * (S.card + 1) ^ q * (q * q) ∧
      ∀ p : Pattern q S, HasRealization H G S R' p → HasDisjoint H G S R' p q := by
  have hle : (liveSet H G S R).card ≤ 2 ^ q * (S.card + 1) ^ q := by
    calc (liveSet H G S R).card ≤ Fintype.card (Pattern q S) := card_le_univ _
      _ = 2 ^ q * (S.card + 1) ^ q := card_pattern q S
  exact clean_all_aux H G S (2 ^ q * (S.card + 1) ^ q) R hle

end PatternCleaning

section ApexBlowup

abbrev BlowupV {n : ℕ} (S R' : Finset (Fin n)) (t r : ℕ) :=
  (S ⊕ (Fin t × R')) ⊕ Fin r

def blowup {n : ℕ} (G : SimpleGraph (Fin n)) (S R' : Finset (Fin n)) (t r : ℕ) :
    SimpleGraph (BlowupV S R' t r) where
  Adj u v := match u, v with
    | Sum.inl (Sum.inl s₁), Sum.inl (Sum.inl s₂) => G.Adj s₁.1 s₂.1
    | Sum.inl (Sum.inl s), Sum.inl (Sum.inr (_, x)) => G.Adj s.1 x.1
    | Sum.inl (Sum.inr (_, x)), Sum.inl (Sum.inl s) => G.Adj x.1 s.1
    | Sum.inl (Sum.inr (i, x)), Sum.inl (Sum.inr (j, y)) => i = j ∧ G.Adj x.1 y.1
    | _, _ => False
  symm := ⟨by
    rintro ((s₁ | ⟨i, x⟩) | a) ((s₂ | ⟨j, y⟩) | b) h
    · exact h.symm
    · exact h.symm
    · exact h.elim
    · exact h.symm
    · exact ⟨h.1.symm, h.2.symm⟩
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · exact h.elim⟩
  loopless := ⟨by
    rintro ((s | ⟨i, x⟩) | a) h
    · exact G.loopless.irrefl s.1 h
    · exact G.loopless.irrefl x.1 h.2
    · exact h.elim⟩

private theorem blowup_free {q n : ℕ} (H : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (S R' : Finset (Fin n)) (t r : ℕ) (hn : 0 < n)
    (hfree : H.Free G) (hactive : ∀ v, ¬ H.IsIsolated v) (hdisjSR : Disjoint S R')
    (hclean : ∀ p : Pattern q S, HasRealization H G S R' p → HasDisjoint H G S R' p q) :
    H.Free (blowup G S R' t r) := by
  rintro ⟨ϕ⟩
  have hnoIso : ∀ v : Fin q, ∃ z : S ⊕ (Fin t × R'), ϕ v = Sum.inl z := by
    intro v
    obtain ⟨w, hvw⟩ := exists_adj_iff_not_isIsolated.mpr (hactive v)
    have hadj := ϕ.toHom.map_rel' hvw
    cases hv : ϕ v with
    | inl z => exact ⟨z, rfl⟩
    | inr k =>
      change (blowup G S R' t r).Adj (ϕ v) (ϕ w) at hadj
      rw [hv] at hadj
      cases ϕ w <;> exact False.elim hadj
  choose ϕ₀ hϕ₀ using hnoIso
  have hϕ₀_inj : Function.Injective ϕ₀ := by
    intro u v eq
    apply ϕ.injective
    change ϕ u = ϕ v
    rw [hϕ₀ u, hϕ₀ v, eq]
  have hϕ₀_adj : ∀ {u v : Fin q}, H.Adj u v →
      (blowup G S R' t r).Adj (Sum.inl (ϕ₀ u)) (Sum.inl (ϕ₀ v)) := by
    intro u v h
    have hadj := ϕ.toHom.map_rel' h
    change (blowup G S R' t r).Adj (ϕ u) (ϕ v) at hadj
    rwa [hϕ₀ u, hϕ₀ v] at hadj
  let attach : Fin q → Option S := fun v =>
    match ϕ₀ v with
    | Sum.inl s => some s
    | Sum.inr _ => none
  let B : Finset (Fin q) := univ.filter (fun v => attach v = none)
  let HB := H.induce (B : Set (Fin q))
  have hmemB : ∀ v, v ∈ B ↔ ∃ p : Fin t × R', ϕ₀ v = Sum.inr p := by
    intro v
    simp only [B, mem_filter, mem_univ, true_and, attach]
    cases ϕ₀ v with
    | inl s => simp
    | inr p => simp
  let compOf : Fin q → Finset (Fin q) := fun v =>
    B.filter (fun w => ∃ hv : v ∈ B, ∃ hw : w ∈ B, HB.Reachable ⟨v, hv⟩ ⟨w, hw⟩)
  let Comps : Finset (Finset (Fin q)) := B.image compOf
  have hcomp_self : ∀ v ∈ B, v ∈ compOf v := by
    intro v hv
    exact mem_filter.mpr ⟨hv, ⟨hv, hv, SimpleGraph.Reachable.refl _⟩⟩
  have hcomp_sub : ∀ C ∈ Comps, C ⊆ B := by
    intro C hC
    obtain ⟨v, _, rfl⟩ := mem_image.mp hC
    exact filter_subset _ _
  have hcomp_nonempty : ∀ C ∈ Comps, C.Nonempty := by
    intro C hC
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hC
    exact ⟨v, hcomp_self v hv⟩
  have hcomp_eq_or_disj : ∀ C₁ ∈ Comps, ∀ C₂ ∈ Comps, C₁ = C₂ ∨ Disjoint C₁ C₂ := by
    intro C₁ hC₁ C₂ hC₂
    obtain ⟨v₁, hv₁, rfl⟩ := mem_image.mp hC₁
    obtain ⟨v₂, hv₂, rfl⟩ := mem_image.mp hC₂
    by_cases hr : HB.Reachable ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩
    · left
      ext w
      simp only [compOf, mem_filter]
      constructor
      · rintro ⟨hw, ⟨_, _, h1w⟩⟩
        exact ⟨hw, ⟨hv₂, hw, hr.symm.trans h1w⟩⟩
      · rintro ⟨hw, ⟨_, _, h2w⟩⟩
        exact ⟨hw, ⟨hv₁, hw, hr.trans h2w⟩⟩
    · right
      rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      obtain ⟨_, ⟨_, _, h1w⟩⟩ := mem_filter.mp hw₁
      obtain ⟨_, ⟨_, _, h2w⟩⟩ := mem_filter.mp hw₂
      exact hr (h1w.trans h2w.symm)
  have hcomp_same_copy : ∀ {a b : ↥(B : Set (Fin q))},
      HB.Reachable a b →
      ∀ (p₁ p₂ : Fin t × R'), ϕ₀ a.1 = Sum.inr p₁ → ϕ₀ b.1 = Sum.inr p₂ → p₁.1 = p₂.1 := by
    intro a b hreach
    obtain ⟨walk⟩ := hreach
    induction walk with
    | nil =>
      intro p₁ p₂ h1 h2
      have := h1.symm.trans h2
      exact congrArg Prod.fst (Sum.inr.inj this)
    | @cons x y z hxy tail ih =>
      intro p₁ p₂ h1 h2
      obtain ⟨pm, hm⟩ := (hmemB y.1).mp y.2
      have hadj := hϕ₀_adj (show H.Adj x.1 y.1 from hxy)
      rw [h1, hm] at hadj
      change p₁.1 = pm.1 ∧ G.Adj p₁.2.1 pm.2.1 at hadj
      exact hadj.1.trans (ih pm p₂ hm h2)
  have hcomp_real : ∀ C ∈ Comps, HasRealization H G S R' (C, attach) := by
    intro C hC
    obtain ⟨v₀, hv₀, rfl⟩ := mem_image.mp hC
    obtain ⟨⟨i₀, r₀⟩, hr₀⟩ := (hmemB v₀).mp hv₀
    let f : Fin q → Fin n := fun u =>
      match ϕ₀ u with
      | Sum.inl _ => r₀.1
      | Sum.inr (_, x) => x.1
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro u hu
      have huB : u ∈ B := (mem_filter.mp hu).1
      obtain ⟨⟨iu, xu⟩, hxu⟩ := (hmemB u).mp huB
      simp [f, hxu, xu.2]
    · intro u hu v hv eq
      obtain ⟨huB, ⟨_, _, hru⟩⟩ := mem_filter.mp hu
      obtain ⟨hvB, ⟨_, _, hrv⟩⟩ := mem_filter.mp hv
      obtain ⟨⟨iu, xu⟩, hxu⟩ := (hmemB u).mp huB
      obtain ⟨⟨iv, xv⟩, hxv⟩ := (hmemB v).mp hvB
      have hi1 : i₀ = iu := hcomp_same_copy hru (i₀, r₀) (iu, xu) hr₀ hxu
      have hi2 : i₀ = iv := hcomp_same_copy hrv (i₀, r₀) (iv, xv) hr₀ hxv
      have hx : xu = xv := Subtype.ext (by simpa [f, hxu, hxv] using eq)
      apply hϕ₀_inj
      rw [hxu, hxv, ← hi1, ← hi2, hx]
    · intro u hu v hv huv
      have huB : u ∈ B := (mem_filter.mp hu).1
      have hvB : v ∈ B := (mem_filter.mp hv).1
      obtain ⟨⟨iu, xu⟩, hxu⟩ := (hmemB u).mp huB
      obtain ⟨⟨iv, xv⟩, hxv⟩ := (hmemB v).mp hvB
      have hadj := hϕ₀_adj huv
      rw [hxu, hxv] at hadj
      change iu = iv ∧ G.Adj xu.1 xv.1 at hadj
      simpa [f, hxu, hxv] using hadj.2
    · intro u hu a s ha hua
      have huB : u ∈ B := (mem_filter.mp hu).1
      obtain ⟨⟨iu, xu⟩, hxu⟩ := (hmemB u).mp huB
      have hϕa : ϕ₀ a = Sum.inl s := by
        dsimp [attach] at ha
        cases h : ϕ₀ a with
        | inl s' =>
          rw [h] at ha
          exact congrArg Sum.inl (Option.some.inj ha)
        | inr _ => rw [h] at ha; cases ha
      have hadj := hϕ₀_adj hua
      rw [hxu, hϕa] at hadj
      change G.Adj xu.1 s.1 at hadj
      simpa [f, hxu] using hadj
  have hgreedy : ∀ L : Finset (Finset (Fin q)), L ⊆ Comps →
      ∃ g : Fin q → Fin n,
        (∀ C ∈ L, IsRealization H G S R' (C, attach) g) ∧
        Set.InjOn g ((L.biUnion id : Finset (Fin q)) : Set (Fin q)) := by
    intro L
    induction L using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ⟨0, hn⟩, by simp, by simp⟩
    | @insert C₀ L hC₀L ih =>
      intro hsubL
      have hC₀ : C₀ ∈ Comps := hsubL (mem_insert_self _ _)
      have hL : L ⊆ Comps := (subset_insert C₀ L).trans hsubL
      obtain ⟨g, hg_real, hg_inj⟩ := ih hL
      let U₀ : Finset (Fin q) := L.biUnion id
      have hdisjC₀U₀ : Disjoint C₀ U₀ := by
        rw [Finset.disjoint_left]
        intro x hxC₀ hxU₀
        obtain ⟨C, hCL, hxC⟩ := mem_biUnion.mp hxU₀
        rcases hcomp_eq_or_disj C₀ hC₀ C (hL hCL) with rfl | hd
        · exact hC₀L hCL
        · exact Finset.disjoint_left.mp hd hxC₀ hxC
      have hU₀_lt : U₀.card < q := by
        have hne : 0 < C₀.card := card_pos.mpr (hcomp_nonempty C₀ hC₀)
        have hle : C₀.card + U₀.card ≤ q := by
          rw [← card_union_of_disjoint hdisjC₀U₀]
          simpa only [Fintype.card_fin] using card_le_univ (C₀ ∪ U₀)
        omega
      let used : Finset (Fin n) := U₀.image g
      have hused_lt : used.card < q := card_image_le.trans_lt hU₀_lt
      obtain ⟨F, hF_real, hF_disj⟩ := hclean (C₀, attach) (hcomp_real C₀ hC₀)
      have hex_i : ∃ i : Fin q, Disjoint (C₀.image (F i)) used := by
        by_contra! hall
        have hpick : ∀ i : Fin q, ∃ y : used, y.1 ∈ C₀.image (F i) := by
          intro i
          have hnd := hall i
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨y, hy1, hy2⟩ := hnd
          exact ⟨⟨y, hy2⟩, hy1⟩
        choose pick hpick using hpick
        have hinj_pick : Function.Injective pick := by
          intro i j eq
          by_contra hne
          obtain ⟨u, hu, h1⟩ := mem_image.mp (hpick i)
          obtain ⟨v, hv, h2⟩ := mem_image.mp (hpick j)
          exact hF_disj i j hne u hu v hv (h1.trans ((congrArg Subtype.val eq).trans h2.symm))
        have hcard := Fintype.card_le_of_injective pick hinj_pick
        simp only [Fintype.card_fin, Fintype.card_coe] at hcard
        omega
      obtain ⟨i₀, hi₀⟩ := hex_i
      let g' : Fin q → Fin n := fun u => if u ∈ C₀ then F i₀ u else g u
      refine ⟨g', ?_, ?_⟩
      · intro C hC
        rcases mem_insert.mp hC with rfl | hCL
        · have hr := hF_real i₀
          refine ⟨fun u hu => by simp [g', hu, hr.1 u hu],
            fun u hu v hv eq => hr.2.1 hu hv (by
              have hu' : u ∈ C := mem_coe.mp hu
              have hv' : v ∈ C := mem_coe.mp hv
              simpa [g', hu', hv'] using eq),
            fun u hu v hv huv => by simpa [g', hu, hv] using hr.2.2.1 u hu v hv huv,
            fun u hu a s ha hua => by simpa [g', hu] using hr.2.2.2 u hu a s ha hua⟩
        · have hdisjCC₀ : Disjoint C C₀ := by
            rcases hcomp_eq_or_disj C (hL hCL) C₀ hC₀ with rfl | hd
            · exact (hC₀L hCL).elim
            · exact hd
          have hnotC₀ : ∀ u ∈ C, u ∉ C₀ := fun u hu => Finset.disjoint_left.mp hdisjCC₀ hu
          have hr := hg_real C hCL
          refine ⟨fun u hu => by simp [g', hnotC₀ u hu, hr.1 u hu],
            fun u hu v hv eq => hr.2.1 hu hv (by
              have hu' : u ∈ C := mem_coe.mp hu
              have hv' : v ∈ C := mem_coe.mp hv
              simpa [g', hnotC₀ u hu', hnotC₀ v hv'] using eq),
            fun u hu v hv huv => by simpa [g', hnotC₀ u hu, hnotC₀ v hv] using hr.2.2.1 u hu v hv huv,
            fun u hu a s ha hua => by simpa [g', hnotC₀ u hu] using hr.2.2.2 u hu a s ha hua⟩
      · intro u hu v hv eq
        rw [biUnion_insert, id_eq, mem_coe, mem_union] at hu hv
        rcases hu with huC₀ | huU₀ <;> rcases hv with hvC₀ | hvU₀
        · exact (hF_real i₀).2.1 huC₀ hvC₀ (by simpa [g', huC₀, hvC₀] using eq)
        · have hvnot : v ∉ C₀ := Finset.disjoint_right.mp hdisjC₀U₀ hvU₀
          simp only [g', if_pos huC₀, if_neg hvnot] at eq
          have h1 : F i₀ u ∈ C₀.image (F i₀) := mem_image_of_mem _ huC₀
          have h2 : F i₀ u ∈ used := eq ▸ mem_image_of_mem _ hvU₀
          exact (Finset.disjoint_left.mp hi₀ h1 h2).elim
        · have hunot : u ∉ C₀ := Finset.disjoint_right.mp hdisjC₀U₀ huU₀
          simp only [g', if_neg hunot, if_pos hvC₀] at eq
          have h1 : F i₀ v ∈ C₀.image (F i₀) := mem_image_of_mem _ hvC₀
          have h2 : F i₀ v ∈ used := eq ▸ mem_image_of_mem _ huU₀
          exact (Finset.disjoint_left.mp hi₀ h1 h2).elim
        · have hunot : u ∉ C₀ := Finset.disjoint_right.mp hdisjC₀U₀ huU₀
          have hvnot : v ∉ C₀ := Finset.disjoint_right.mp hdisjC₀U₀ hvU₀
          exact hg_inj huU₀ hvU₀ (by simpa [g', hunot, hvnot] using eq)
  obtain ⟨g, hg_real, hg_inj⟩ := hgreedy Comps Subset.rfl
  have hbiUnion : Comps.biUnion id = B := by
    ext v
    simp only [mem_biUnion, id_eq]
    constructor
    · rintro ⟨C, hC, hv⟩
      exact hcomp_sub C hC hv
    · intro hv
      exact ⟨compOf v, mem_image_of_mem _ hv, hcomp_self v hv⟩
  rw [hbiUnion] at hg_inj
  let Φ : Fin q → Fin n := fun v =>
    match attach v with
    | some s => s.1
    | none => g v
  have hΦ_A : ∀ v s, attach v = some s → Φ v = s.1 ∧ ϕ₀ v = Sum.inl s := by
    intro v s hv
    refine ⟨by simp [Φ, hv], ?_⟩
    dsimp [attach] at hv
    cases h : ϕ₀ v with
    | inl s' => rw [h] at hv; exact congrArg Sum.inl (Option.some.inj hv)
    | inr _ => rw [h] at hv; cases hv
  have hΦ_B : ∀ v, attach v = none → Φ v = g v ∧ v ∈ B ∧ g v ∈ R' := by
    intro v hv
    have hvB : v ∈ B := mem_filter.mpr ⟨mem_univ _, hv⟩
    have hC : compOf v ∈ Comps := mem_image_of_mem _ hvB
    exact ⟨by simp [Φ, hv], hvB, (hg_real _ hC).1 v (hcomp_self v hvB)⟩
  have hΦ_inj : Function.Injective Φ := by
    intro u v eq
    cases hu : attach u with
    | some su =>
      obtain ⟨hΦu, hϕu⟩ := hΦ_A u su hu
      cases hv : attach v with
      | some sv =>
        obtain ⟨hΦv, hϕv⟩ := hΦ_A v sv hv
        rw [hΦu, hΦv] at eq
        apply hϕ₀_inj
        rw [hϕu, hϕv, Subtype.ext eq]
      | none =>
        obtain ⟨hΦv, _, hgvR⟩ := hΦ_B v hv
        rw [hΦu, hΦv] at eq
        exact (Finset.disjoint_left.mp hdisjSR su.2 (eq ▸ hgvR)).elim
    | none =>
      obtain ⟨hΦu, huB, hguR⟩ := hΦ_B u hu
      cases hv : attach v with
      | some sv =>
        obtain ⟨hΦv, _⟩ := hΦ_A v sv hv
        rw [hΦu, hΦv] at eq
        exact (Finset.disjoint_left.mp hdisjSR sv.2 (eq.symm ▸ hguR)).elim
      | none =>
        obtain ⟨hΦv, hvB, _⟩ := hΦ_B v hv
        rw [hΦu, hΦv] at eq
        exact hg_inj huB hvB eq
  have hΦ_hom : ∀ {u v : Fin q}, H.Adj u v → G.Adj (Φ u) (Φ v) := by
    intro u v huv
    cases hu : attach u with
    | some su =>
      obtain ⟨hΦu, hϕu⟩ := hΦ_A u su hu
      cases hv : attach v with
      | some sv =>
        obtain ⟨hΦv, hϕv⟩ := hΦ_A v sv hv
        have hadj := hϕ₀_adj huv
        rw [hϕu, hϕv] at hadj
        rw [hΦu, hΦv]
        exact hadj
      | none =>
        obtain ⟨hΦv, hvB, _⟩ := hΦ_B v hv
        have hC : compOf v ∈ Comps := mem_image_of_mem _ hvB
        rw [hΦu, hΦv]
        exact ((hg_real _ hC).2.2.2 v (hcomp_self v hvB) u su hu huv.symm).symm
    | none =>
      obtain ⟨hΦu, huB, _⟩ := hΦ_B u hu
      cases hv : attach v with
      | some sv =>
        obtain ⟨hΦv, _⟩ := hΦ_A v sv hv
        have hC : compOf u ∈ Comps := mem_image_of_mem _ huB
        rw [hΦu, hΦv]
        exact (hg_real _ hC).2.2.2 u (hcomp_self u huB) v sv hv huv
      | none =>
        obtain ⟨hΦv, hvB, _⟩ := hΦ_B v hv
        have hC : compOf u ∈ Comps := mem_image_of_mem _ huB
        have hvC : v ∈ compOf u :=
          mem_filter.mpr ⟨hvB, ⟨huB, hvB, SimpleGraph.Adj.reachable (show HB.Adj ⟨u, huB⟩ ⟨v, hvB⟩ from huv)⟩⟩
        rw [hΦu, hΦv]
        exact (hg_real _ hC).2.2.1 u (hcomp_self u huB) v hvC huv
  exact hfree ⟨⟨⟨Φ, fun h => hΦ_hom h⟩, hΦ_inj⟩⟩

private theorem blowup_edge_card_ge {n : ℕ} (G : SimpleGraph (Fin n))
    (S R' : Finset (Fin n)) (t r : ℕ) (hdisj : Disjoint S R') :
    t * (G.edgeFinset.filter (fun e => ∃ u ∈ R', ∃ v ∈ S ∪ R', e = s(u, v))).card ≤
      (blowup G S R' t r).edgeFinset.card := by
  let Egood := G.edgeFinset.filter (fun e => ∃ u ∈ R', ∃ v ∈ S ∪ R', e = s(u, v))
  let embed (i : Fin t) (x : ↥(S ∪ R')) : BlowupV S R' t r :=
    if hx : x.1 ∈ S then Sum.inl (Sum.inl ⟨x.1, hx⟩)
    else Sum.inl (Sum.inr (i, ⟨x.1, (mem_union.mp x.2).resolve_left hx⟩))
  let proj : BlowupV S R' t r → Option (Fin n)
    | Sum.inl (Sum.inl s) => some s.1
    | Sum.inl (Sum.inr (_, x)) => some x.1
    | Sum.inr _ => none
  let copyIdx : BlowupV S R' t r → Option (Fin t)
    | Sum.inl (Sum.inr (i, _)) => some i
    | _ => none
  have hproj (i : Fin t) (x : ↥(S ∪ R')) : proj (embed i x) = some x.1 := by
    dsimp [embed]
    split_ifs <;> rfl
  have hcopy_le (i : Fin t) (x : ↥(S ∪ R')) :
      copyIdx (embed i x) = none ∨ copyIdx (embed i x) = some i := by
    dsimp [embed]
    split_ifs <;> simp [copyIdx]
  have hcopy_R (i : Fin t) (u : Fin n) (hu : u ∈ R') :
      copyIdx (embed i ⟨u, mem_union_right _ hu⟩) = some i := by
    have hunotS : u ∉ S := Finset.disjoint_right.mp hdisj hu
    simp [embed, hunotS, copyIdx]
  have hegood_spec (e : Egood) : ∃ u ∈ R', ∃ v ∈ S ∪ R', e.1 = s(u, v) :=
    (mem_filter.mp e.2).2
  choose eu heu ev hev heq using hegood_spec
  let liftEdge (p : Fin t × Egood) : (blowup G S R' t r).edgeFinset :=
    ⟨s(embed p.1 ⟨eu p.2, mem_union_right _ (heu p.2)⟩, embed p.1 ⟨ev p.2, hev p.2⟩), by
      rw [mem_edgeFinset]
      have hadj : G.Adj (eu p.2) (ev p.2) := by
        have hmem := (mem_filter.mp p.2.2).1
        rw [heq p.2, mem_edgeFinset] at hmem
        exact hmem
      have hunotS : eu p.2 ∉ S := Finset.disjoint_right.mp hdisj (heu p.2)
      dsimp [embed]
      rw [dif_neg hunotS]
      split_ifs with hvS
      · exact hadj
      · exact ⟨rfl, hadj⟩⟩
  have hlift_inj : Function.Injective liftEdge := by
    rintro ⟨i₁, e₁⟩ ⟨i₂, e₂⟩ h
    have hval : s(embed i₁ ⟨eu e₁, mem_union_right _ (heu e₁)⟩, embed i₁ ⟨ev e₁, hev e₁⟩) =
        s(embed i₂ ⟨eu e₂, mem_union_right _ (heu e₂)⟩, embed i₂ ⟨ev e₂, hev e₂⟩) :=
      congrArg Subtype.val h
    have he : e₁ = e₂ := by
      have hm := congrArg (Sym2.map proj) hval
      simp only [Sym2.map_mk, hproj] at hm
      have hm' : Sym2.map Option.some e₁.1 = Sym2.map Option.some e₂.1 := by
        rw [heq e₁, heq e₂, Sym2.map_mk, Sym2.map_mk]
        exact hm
      have hsym : e₁.1 = e₂.1 := (Sym2.map.injective (Option.some_injective (Fin n))) hm'
      exact Subtype.ext hsym
    have hi : i₁ = i₂ := by
      have hm := congrArg (Sym2.map copyIdx) hval
      have hmem1 : some i₁ ∈ Sym2.map copyIdx
          s(embed i₁ ⟨eu e₁, mem_union_right _ (heu e₁)⟩, embed i₁ ⟨ev e₁, hev e₁⟩) := by
        rw [Sym2.map_mk, hcopy_R i₁ (eu e₁) (heu e₁)]
        exact Sym2.mem_mk_left _ _
      rw [hm, Sym2.map_mk, Sym2.mem_iff] at hmem1
      rcases hmem1 with h1 | h2
      · rw [hcopy_R i₂ (eu e₂) (heu e₂)] at h1
        exact Option.some.inj h1
      · rcases hcopy_le i₂ ⟨ev e₂, hev e₂⟩ with hnone | hsome
        · rw [hnone] at h2; cases h2
        · rw [hsome] at h2; exact Option.some.inj h2
    exact Prod.ext hi he
  have hcard := Fintype.card_le_of_injective liftEdge hlift_inj
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hcard
  exact hcard

end ApexBlowup

section DegreeGap

private noncomputable def Mbound (C : ℕ) (d : ℚ) : ℕ :=
  Nat.floor (2 * (C : ℚ) / d)

private noncomputable def deltaSeq (q C : ℕ) (ε : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
      let d := deltaSeq q C ε k
      let M := Mbound C d
      min (d / 2) (ε / (4 * ((2 ^ q * (M + 1) ^ q * (q * q) : ℕ) + 1 : ℚ)))

private theorem deltaSeq_pos (q C : ℕ) {ε : ℚ} (hε : 0 < ε) : ∀ k, 0 < deltaSeq q C ε k
  | 0 => by simp [deltaSeq]
  | k + 1 => by
    have hk := deltaSeq_pos q C hε k
    simp only [deltaSeq, lt_min_iff]
    constructor
    · linarith
    · positivity

private theorem deltaSeq_succ_lt (q C : ℕ) {ε : ℚ} (hε : 0 < ε) (k : ℕ) :
    deltaSeq q C ε (k + 1) < deltaSeq q C ε k := by
  have hk := deltaSeq_pos q C hε k
  calc deltaSeq q C ε (k + 1) ≤ deltaSeq q C ε k / 2 := min_le_left _ _
    _ < deltaSeq q C ε k := by linarith

private theorem deltaSeq_strictAnti (q C : ℕ) {ε : ℚ} (hε : 0 < ε) :
    StrictAnti (deltaSeq q C ε) :=
  strictAnti_nat_of_succ_lt (deltaSeq_succ_lt q C hε)

private theorem Mbound_mono (q C : ℕ) {ε : ℚ} (hε : 0 < ε) {i j : ℕ} (hij : i ≤ j) :
    Mbound C (deltaSeq q C ε i) ≤ Mbound C (deltaSeq q C ε j) := by
  apply Nat.floor_mono
  have hle : deltaSeq q C ε j ≤ deltaSeq q C ε i := (deltaSeq_strictAnti q C hε).antitone hij
  have hpos : 0 < deltaSeq q C ε j := deltaSeq_pos q C hε j
  exact div_le_div_of_nonneg_left (by positivity) hpos hle

private theorem deltaSeq_clean_bound (q C : ℕ) {ε : ℚ} (hε : 0 < ε) (k : ℕ) :
    ((2 ^ q * (Mbound C (deltaSeq q C ε k) + 1) ^ q * (q * q) : ℕ) : ℚ) *
      deltaSeq q C ε (k + 1) ≤ ε / 4 := by
  set P : ℕ := 2 ^ q * (Mbound C (deltaSeq q C ε k) + 1) ^ q * (q * q)
  have hle : deltaSeq q C ε (k + 1) ≤ ε / (4 * ((P : ℚ) + 1)) := min_le_right _ _
  have hP0 : (0 : ℚ) ≤ P := Nat.cast_nonneg P
  have hden : (0 : ℚ) < 4 * ((P : ℚ) + 1) := by positivity
  calc (P : ℚ) * deltaSeq q C ε (k + 1)
      ≤ (P : ℚ) * (ε / (4 * ((P : ℚ) + 1))) := mul_le_mul_of_nonneg_left hle hP0
    _ ≤ ((P : ℚ) + 1) * (ε / (4 * ((P : ℚ) + 1))) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε / 4 := by field_simp

private theorem transfer_of_linear {q : ℕ} (H : SimpleGraph (Fin q))
    (edges : 2 ≤ H.edgeFinset.card) (active : ∀ v, ¬ H.IsIsolated v)
    (C : ℕ) (cap : ∀ᶠ n : ℕ in atTop, extremalNumber n H ≤ C * n)
    (a b : ℚ) (ha : 0 < a) (hab : a < b)
    (often : ∀ N, ∃ n ≥ N, b * n < (extremalNumber n H : ℚ)) :
    ∃ M, ∀ m ≥ M, a * m ≤ (extremalNumber m H : ℚ) := by
  have hHne : H ≠ ⊥ := by
    intro h
    rw [edgeFinset_eq_empty.mpr h] at edges
    simp at edges
  let ε : ℚ := (b - a) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let L : ℕ := Nat.ceil (8 * (C : ℚ) / ε) + 1
  have hLpos : 0 < L := Nat.succ_pos _
  have hL_bound : 2 * (C : ℚ) / (L : ℚ) ≤ ε / 4 := by
    have hL1 : 8 * (C : ℚ) / ε ≤ (L : ℚ) := by
      have hc : 8 * (C : ℚ) / ε ≤ (Nat.ceil (8 * (C : ℚ) / ε) : ℚ) := Nat.le_ceil _
      have hcast : (Nat.ceil (8 * (C : ℚ) / ε) : ℚ) ≤ (L : ℚ) := by
        dsimp [L]; push_cast; linarith
      exact hc.trans hcast
    have hLposQ : (0 : ℚ) < L := by exact_mod_cast hLpos
    rw [div_le_iff₀ hLposQ]
    have hmul := (div_le_iff₀ hε).mp hL1
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp cap
  let ML : ℕ := Mbound C (deltaSeq q C ε L)
  let N : ℕ := max (max N₀ 1) (Nat.ceil (4 * ((ML * ML : ℕ) : ℚ) / ε))
  obtain ⟨n, hnN, hbn⟩ := often N
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hnN)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hnN)
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hML_bound : ((ML * ML : ℕ) : ℚ) ≤ (ε / 4) * n := by
    have hc : 4 * ((ML * ML : ℕ) : ℚ) / ε ≤ (n : ℚ) := by
      have h1 : Nat.ceil (4 * ((ML * ML : ℕ) : ℚ) / ε) ≤ n := (le_max_right _ _).trans hnN
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hmul := (div_le_iff₀ hε).mp hc
    linarith
  obtain ⟨G, dG, hGext⟩ := exists_isExtremal_free (V := Fin n) hHne
  let _ : DecidableRel G.Adj := dG
  have hGfree : H.Free G := hGext.prop
  have hGcard : G.edgeFinset.card = extremalNumber n H := by
    simpa only [Fintype.card_fin] using card_edgeFinset_of_isExtremal_free hGext
  have hGle : G.edgeFinset.card ≤ C * n := hGcard.le.trans (hN₀ n hn0)
  have hGgt : b * n < (G.edgeFinset.card : ℚ) := hGcard ▸ hbn
  let shell (k : Fin L) : Finset (Fin n) :=
    univ.filter (fun v =>
      deltaSeq q C ε (k.1 + 1) * n ≤ (G.degree v : ℚ) ∧
      (G.degree v : ℚ) < deltaSeq q C ε k.1 * n)
  have hshell_disj : Set.PairwiseDisjoint ((univ : Finset (Fin L)) : Set (Fin L)) shell := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvi hvj
    obtain ⟨_, hi1, hi2⟩ := mem_filter.mp hvi
    obtain ⟨_, hj1, hj2⟩ := mem_filter.mp hvj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · have hd : deltaSeq q C ε j.1 ≤ deltaSeq q C ε (i.1 + 1) :=
        (deltaSeq_strictAnti q C hε).antitone (by omega)
      have hmul : deltaSeq q C ε j.1 * n ≤ deltaSeq q C ε (i.1 + 1) * n :=
        mul_le_mul_of_nonneg_right hd hnpos.le
      linarith
    · have hd : deltaSeq q C ε i.1 ≤ deltaSeq q C ε (j.1 + 1) :=
        (deltaSeq_strictAnti q C hε).antitone (by omega)
      have hmul : deltaSeq q C ε i.1 * n ≤ deltaSeq q C ε (j.1 + 1) * n :=
        mul_le_mul_of_nonneg_right hd hnpos.le
      linarith
  have hsum_shells : ∑ k : Fin L, ∑ v ∈ shell k, G.degree v ≤ 2 * C * n := by
    rw [← sum_biUnion hshell_disj]
    calc ∑ v ∈ (univ : Finset (Fin L)).biUnion shell, G.degree v
        ≤ ∑ v : Fin n, G.degree v := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * (C * n) := Nat.mul_le_mul_left 2 hGle
      _ = 2 * C * n := (Nat.mul_assoc 2 C n).symm
  have hex_k : ∃ k : Fin L, L * (∑ v ∈ shell k, G.degree v) ≤ 2 * C * n := by
    by_contra! hall
    have hlt : ∑ _k : Fin L, (2 * C * n) < ∑ k : Fin L, L * (∑ v ∈ shell k, G.degree v) :=
      sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr ⟨⟨0, hLpos⟩⟩) (fun k _ => hall k)
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum] at hlt
    have hle : L * ∑ k : Fin L, ∑ v ∈ shell k, G.degree v ≤ L * (2 * C * n) :=
      Nat.mul_le_mul_left L hsum_shells
    omega
  obtain ⟨k, hk⟩ := hex_k
  have hA_deg : ((∑ v ∈ shell k, G.degree v : ℕ) : ℚ) ≤ (ε / 4) * n := by
    have hkQ : (L : ℚ) * ((∑ v ∈ shell k, G.degree v : ℕ) : ℚ) ≤ 2 * (C : ℚ) * n := by
      exact_mod_cast hk
    have hLposQ : (0 : ℚ) < L := by exact_mod_cast hLpos
    have h1 : ((∑ v ∈ shell k, G.degree v : ℕ) : ℚ) ≤ (2 * (C : ℚ) / L) * n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hLposQ]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hL_bound hnpos.le)
  let S : Finset (Fin n) := univ.filter (fun v => deltaSeq q C ε k.1 * n ≤ (G.degree v : ℚ))
  let A : Finset (Fin n) := shell k
  let R : Finset (Fin n) := univ.filter (fun v => (G.degree v : ℚ) < deltaSeq q C ε (k.1 + 1) * n)
  have hdisjSR : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro v hvS hvR
    have h1 := (mem_filter.mp hvS).2
    have h2 := (mem_filter.mp hvR).2
    have hd : deltaSeq q C ε (k.1 + 1) < deltaSeq q C ε k.1 := deltaSeq_succ_lt q C hε k.1
    have hmul : deltaSeq q C ε (k.1 + 1) * n < deltaSeq q C ε k.1 * n :=
      mul_lt_mul_of_pos_right hd hnpos
    linarith
  have hScard : S.card ≤ Mbound C (deltaSeq q C ε k.1) := by
    have hsumS : ∑ v ∈ S, G.degree v ≤ 2 * C * n := by
      calc ∑ v ∈ S, G.degree v
          ≤ ∑ v : Fin n, G.degree v := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
        _ ≤ 2 * (C * n) := Nat.mul_le_mul_left 2 hGle
        _ = 2 * C * n := (Nat.mul_assoc 2 C n).symm
    have hlow : (S.card : ℚ) * (deltaSeq q C ε k.1 * n) ≤ ((∑ v ∈ S, G.degree v : ℕ) : ℚ) := by
      rw [Nat.cast_sum]
      calc (S.card : ℚ) * (deltaSeq q C ε k.1 * n)
          = ∑ _v ∈ S, (deltaSeq q C ε k.1 * n) := by simp
        _ ≤ ∑ v ∈ S, (G.degree v : ℚ) := sum_le_sum fun v hv => (mem_filter.mp hv).2
    have hsumSQ : ((∑ v ∈ S, G.degree v : ℕ) : ℚ) ≤ 2 * (C : ℚ) * n := by exact_mod_cast hsumS
    have hdk : 0 < deltaSeq q C ε k.1 := deltaSeq_pos q C hε k.1
    have hSrat : (S.card : ℚ) ≤ 2 * (C : ℚ) / deltaSeq q C ε k.1 := by
      rw [le_div_iff₀ hdk]
      have hmul : (S.card : ℚ) * deltaSeq q C ε k.1 * n ≤ (2 * (C : ℚ)) * n := by linarith
      exact le_of_mul_le_mul_right hmul hnpos
    exact Nat.le_floor hSrat
  obtain ⟨R', hR'R, hDcard, hclean⟩ := clean_all H G S R
  let D : Finset (Fin n) := R \ R'
  have hdisjSR' : Disjoint S R' := hdisjSR.mono_right hR'R
  have hD_deg : ((∑ v ∈ D, G.degree v : ℕ) : ℚ) ≤ (ε / 4) * n := by
    have h1 : ((∑ v ∈ D, G.degree v : ℕ) : ℚ) ≤ (D.card : ℚ) * (deltaSeq q C ε (k.1 + 1) * n) := by
      rw [Nat.cast_sum]
      calc ∑ v ∈ D, (G.degree v : ℚ)
          ≤ ∑ _v ∈ D, (deltaSeq q C ε (k.1 + 1) * n) :=
            sum_le_sum fun v hv => ((mem_filter.mp (Finset.mem_sdiff.mp hv).1).2).le
        _ = (D.card : ℚ) * (deltaSeq q C ε (k.1 + 1) * n) := by simp
    have hDnat : D.card ≤ 2 ^ q * (Mbound C (deltaSeq q C ε k.1) + 1) ^ q * (q * q) := by
      apply hDcard.trans
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (Nat.add_le_add_right hScard 1) q
    have hDrat : (D.card : ℚ) ≤ ((2 ^ q * (Mbound C (deltaSeq q C ε k.1) + 1) ^ q * (q * q) : ℕ) : ℚ) := by
      exact_mod_cast hDnat
    have hdk1 : 0 < deltaSeq q C ε (k.1 + 1) := deltaSeq_pos q C hε (k.1 + 1)
    calc ((∑ v ∈ D, G.degree v : ℕ) : ℚ)
        ≤ (D.card : ℚ) * (deltaSeq q C ε (k.1 + 1) * n) := h1
      _ ≤ ((2 ^ q * (Mbound C (deltaSeq q C ε k.1) + 1) ^ q * (q * q) : ℕ) : ℚ) *
            (deltaSeq q C ε (k.1 + 1) * n) :=
          mul_le_mul_of_nonneg_right hDrat (mul_nonneg hdk1.le hnpos.le)
      _ = (((2 ^ q * (Mbound C (deltaSeq q C ε k.1) + 1) ^ q * (q * q) : ℕ) : ℚ) *
            deltaSeq q C ε (k.1 + 1)) * n := (mul_assoc _ _ _).symm
      _ ≤ (ε / 4) * n := mul_le_mul_of_nonneg_right (deltaSeq_clean_bound q C hε k.1) hnpos.le
  let E_S : Finset (Sym2 (Fin n)) := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)
  let E_A : Finset (Sym2 (Fin n)) := A.biUnion (fun v => G.incidenceFinset v)
  let E_D : Finset (Sym2 (Fin n)) := D.biUnion (fun v => G.incidenceFinset v)
  let E_good : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e => ∃ u ∈ R', ∃ v ∈ S ∪ R', e = s(u, v))
  have hE_S_card : E_S.card ≤ S.card * S.card := by
    have hsub : E_S ⊆ S.biUnion (fun u => S.image (fun v => s(u, v))) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hmem := (mem_filter.mp he).2
        have hu : u ∈ S := hmem u (Sym2.mem_mk_left u v)
        have hv : v ∈ S := hmem v (Sym2.mem_mk_right u v)
        exact mem_biUnion.mpr ⟨u, hu, mem_image.mpr ⟨v, hv, rfl⟩⟩
    calc E_S.card ≤ (S.biUnion (fun u => S.image (fun v => s(u, v)))).card := card_le_card hsub
      _ ≤ ∑ u ∈ S, (S.image (fun v => s(u, v))).card := card_biUnion_le
      _ ≤ ∑ _u ∈ S, S.card := sum_le_sum fun _ _ => card_image_le
      _ = S.card * S.card := by simp
  have hE_S_Q : (E_S.card : ℚ) ≤ (ε / 4) * n := by
    have hMkML : Mbound C (deltaSeq q C ε k.1) ≤ ML := Mbound_mono q C hε k.2.le
    have hSML : S.card ≤ ML := hScard.trans hMkML
    have h1 : E_S.card ≤ ML * ML := hE_S_card.trans (Nat.mul_le_mul hSML hSML)
    exact (by exact_mod_cast h1 : (E_S.card : ℚ) ≤ ((ML * ML : ℕ) : ℚ)).trans hML_bound
  have hE_A_Q : (E_A.card : ℚ) ≤ (ε / 4) * n := by
    have h1 : E_A.card ≤ ∑ v ∈ A, G.degree v := by
      calc E_A.card ≤ ∑ v ∈ A, (G.incidenceFinset v).card := card_biUnion_le
        _ = ∑ v ∈ A, G.degree v := by simp [card_incidenceFinset_eq_degree]
    exact (Nat.cast_le.mpr h1).trans hA_deg
  have hE_D_Q : (E_D.card : ℚ) ≤ (ε / 4) * n := by
    have h1 : E_D.card ≤ ∑ v ∈ D, G.degree v := by
      calc E_D.card ≤ ∑ v ∈ D, (G.incidenceFinset v).card := card_biUnion_le
        _ = ∑ v ∈ D, G.degree v := by simp [card_incidenceFinset_eq_degree]
    exact (Nat.cast_le.mpr h1).trans hD_deg
  have hpart : ∀ x : Fin n, x ∈ S ∨ x ∈ A ∨ x ∈ D ∨ x ∈ R' := by
    intro x
    by_cases h1 : deltaSeq q C ε k.1 * n ≤ (G.degree x : ℚ)
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _, h1⟩)
    · by_cases h2 : deltaSeq q C ε (k.1 + 1) * n ≤ (G.degree x : ℚ)
      · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ _, h2, not_le.mp h1⟩))
      · have hxR : x ∈ R := mem_filter.mpr ⟨mem_univ _, not_le.mp h2⟩
        by_cases hxR' : x ∈ R'
        · exact Or.inr (Or.inr (Or.inr hxR'))
        · exact Or.inr (Or.inr (Or.inl (mem_sdiff.mpr ⟨hxR, hxR'⟩)))
  have hcov : G.edgeFinset ⊆ E_S ∪ (E_A ∪ (E_D ∪ E_good)) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := G.mem_edgeFinset.mp he
      by_cases hxA : x ∈ A
      · exact mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨x, hxA,
          (G.mem_incidenceFinset x _).mpr (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩))
      by_cases hyA : y ∈ A
      · exact mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨y, hyA,
          (G.mem_incidenceFinset y _).mpr (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩))
      by_cases hxD : x ∈ D
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨x, hxD,
          (G.mem_incidenceFinset x _).mpr (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩)))
      by_cases hyD : y ∈ D
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨y, hyD,
          (G.mem_incidenceFinset y _).mpr (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩)))
      have hxSR : x ∈ S ∨ x ∈ R' := by
        rcases hpart x with h | h | h | h
        · exact Or.inl h
        · exact (hxA h).elim
        · exact (hxD h).elim
        · exact Or.inr h
      have hySR : y ∈ S ∨ y ∈ R' := by
        rcases hpart y with h | h | h | h
        · exact Or.inl h
        · exact (hyA h).elim
        · exact (hyD h).elim
        · exact Or.inr h
      rcases hxSR with hxS | hxR'
      · rcases hySR with hyS | hyR'
        · refine mem_union_left _ (mem_filter.mpr ⟨he, fun v hv => ?_⟩)
          rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
        · refine mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨he, ?_⟩)))
          exact ⟨y, hyR', x, mem_union_left _ hxS, Sym2.eq_swap⟩
      · refine mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨he, ?_⟩)))
        exact ⟨x, hxR', y, mem_union.mpr hySR, rfl⟩
  have hcard_sum : G.edgeFinset.card ≤ E_S.card + E_A.card + E_D.card + E_good.card := by
    have h1 := card_le_card hcov
    have h2 := card_union_le E_S (E_A ∪ (E_D ∪ E_good))
    have h3 := card_union_le E_A (E_D ∪ E_good)
    have h4 := card_union_le E_D E_good
    omega
  have hEgood_Q : (a + 5 * ε / 4) * n < (E_good.card : ℚ) := by
    have hsumQ : (G.edgeFinset.card : ℚ) ≤ (E_S.card : ℚ) + (E_A.card : ℚ) + (E_D.card : ℚ) + (E_good.card : ℚ) := by
      exact_mod_cast hcard_sum
    have hba : b = a + 2 * ε := by dsimp [ε]; ring
    rw [hba] at hGgt
    linarith
  have hEgood_pos : 0 < E_good.card := by
    by_contra! h0
    have hz : (E_good.card : ℚ) = 0 := by exact_mod_cast Nat.eq_zero_of_le_zero h0
    have hpos_lhs : (0 : ℚ) < (a + 5 * ε / 4) * n := by positivity
    linarith
  have hR'_pos : 0 < R'.card := by
    obtain ⟨e, he⟩ := card_pos.mp hEgood_pos
    obtain ⟨u, hu, _, _, _⟩ := (mem_filter.mp he).2
    exact card_pos.mpr ⟨u, hu⟩
  have hR'_le_n : R'.card ≤ n := by
    simpa only [Fintype.card_fin] using card_le_univ R'
  have hSR'_le_n : S.card + R'.card ≤ n := by
    rw [← card_union_of_disjoint hdisjSR']
    simpa only [Fintype.card_fin] using card_le_univ (S ∪ R')
  have hEgood_R' : (a + 5 * ε / 4) * (R'.card : ℚ) ≤ (E_good.card : ℚ) := by
    have h1 : (a + 5 * ε / 4) * (R'.card : ℚ) ≤ (a + 5 * ε / 4) * (n : ℚ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hR'_le_n) (by positivity)
    exact h1.trans hEgood_Q.le
  let M : ℕ := max n (Nat.ceil (4 * (a + 5 * ε / 4) * (n : ℚ) / (5 * ε)))
  refine ⟨M, fun m hm => ?_⟩
  have hmn : n ≤ m := (le_max_left _ _).trans hm
  have hmS : S.card ≤ m := by omega
  let t : ℕ := (m - S.card) / R'.card
  let r : ℕ := (m - S.card) % R'.card
  have hdiv : R'.card * t + r = m - S.card := Nat.div_add_mod (m - S.card) R'.card
  have hr_lt : r < R'.card := Nat.mod_lt (m - S.card) hR'_pos
  have hVcard : Fintype.card (BlowupV S R' t r) = m := by
    simp only [BlowupV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    have hmul : t * R'.card = R'.card * t := Nat.mul_comm t R'.card
    omega
  have hfree_b : H.Free (blowup G S R' t r) :=
    blowup_free H G S R' t r (by omega) hGfree active hdisjSR' hclean
  have hedge_le : (blowup G S R' t r).edgeFinset.card ≤ extremalNumber m H := by
    have h := card_edgeFinset_le_extremalNumber hfree_b
    rwa [hVcard] at h
  have hedge_ge : t * E_good.card ≤ (blowup G S R' t r).edgeFinset.card := by
    convert blowup_edge_card_ge G S R' t r hdisjSR'
  have h_ex_ge : t * E_good.card ≤ extremalNumber m H := hedge_ge.trans hedge_le
  have htR : m ≤ t * R'.card + n := by
    have hmul : t * R'.card = R'.card * t := Nat.mul_comm t R'.card
    omega
  have htRQ : (m : ℚ) - (n : ℚ) ≤ (t : ℚ) * (R'.card : ℚ) := by
    have h1 : (m : ℚ) ≤ (t : ℚ) * (R'.card : ℚ) + (n : ℚ) := by exact_mod_cast htR
    linarith
  have hm_eta : (a + 5 * ε / 4) * (n : ℚ) ≤ (5 * ε / 4) * (m : ℚ) := by
    have h1 : 4 * (a + 5 * ε / 4) * (n : ℚ) / (5 * ε) ≤ (m : ℚ) := by
      have hceil : Nat.ceil (4 * (a + 5 * ε / 4) * (n : ℚ) / (5 * ε)) ≤ m :=
        (le_max_right _ _).trans hm
      exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have h5e : (0 : ℚ) < 5 * ε := by positivity
    have h2 := (div_le_iff₀ h5e).mp h1
    linarith
  have hQ : (t : ℚ) * (E_good.card : ℚ) ≤ (extremalNumber m H : ℚ) := by exact_mod_cast h_ex_ge
  calc a * (m : ℚ)
      ≤ (a + 5 * ε / 4) * ((m : ℚ) - (n : ℚ)) := by linarith
    _ ≤ (a + 5 * ε / 4) * ((t : ℚ) * (R'.card : ℚ)) :=
        mul_le_mul_of_nonneg_left htRQ (by positivity)
    _ = (t : ℚ) * ((a + 5 * ε / 4) * (R'.card : ℚ)) := by ring
    _ ≤ (t : ℚ) * (E_good.card : ℚ) := mul_le_mul_of_nonneg_left hEgood_R' (Nat.cast_nonneg t)
    _ ≤ (extremalNumber m H : ℚ) := hQ

end DegreeGap

end E713H2Proof

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1.H2 := by
  intro q G _ edges active _ branch linear
  obtain ⟨C, cap⟩ := linear
  obtain ⟨c, hlim⟩ := E713H2Proof.sustained G C cap
    (E713H2Proof.transfer_of_linear G edges active C cap)
  exact ⟨c, E713H2Proof.positive_limit G branch c hlim⟩
