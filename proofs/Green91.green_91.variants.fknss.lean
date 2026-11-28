import FormalConjectures.GreensOpenProblems.«91»
import Mathlib

-- Problem: Ferber, Kwan, Narayanan, Sah and Sawhney (Green's Open Problem 91).
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/91.lean:94 (declaration Green91.green_91.variants.fknss)
-- Credit: @gdyan2022

/-!
Proof of `Green91.green_91.variants.fknss`:
With high probability, `G(n, 1/2)` admits a bisection in which `n - o(n)` vertices are strictly friendly.

Architecture (elementary kicked `C^2` proximal gradient ascent + Efron–Stein concentration):
1. Measure-to-finite-counting bridge (`prob_eq_card_div`, `graphEquiv`) and diagonal extraction.
2. Finite probability toolkit on uniform Boolean cubes: Rademacher Hoeffding (`rademacher_hoeffding`),
   central binomial bound (`choose_div_two_pow_le`), and Efron–Stein variance inequality (`efron_stein_bool`).
3. Typical properties of `G(n, 1/2)`: operator norm bound `‖A / √n‖_op ≤ 20` via an explicit
   integer `1/8`-net (`op_norm_bad_bound`) and uniform anti-concentration across all `2^n`
   bisections (`all_bisections_anticonc`).
4. Explicit closed-form `C^2` proximal map `ψ_λ(z) = (√((z+1)^2 + λ) - √((z-1)^2 + λ)) / 2`,
   its exact inverse `h_λ(u) = u √(1 + λ/(1-u^2))`, convex barrier `R_λ`, degree-5 Hermite cutoff
   `χ_γ`, kick truncation `τ(z) = 2z / √(4 + z^2)`, and exact proximal ascent inequality.
5. Kicked proximal ascent dynamics over `(EdgeIdx n → Bool) × (Fin T → Fin n → Fin n → Bool)`:
   exact `π`-antisymmetry (`E[mean(x_t)] = 0`), `C^2` backpropagation Efron–Stein variance bound
   `Var(mean(x_t)) = O(1/n)`, and pointwise Paley–Zygmund escape from interior vertices.
6. Rounding a nearly-stationary, nearly-integral, nearly-balanced iterate to an exact bisection
   with `≥ (1 - ε) n` strictly friendly vertices, yielding `OMA.solution`.
-/

namespace Green91FKNSS

open Finset Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

/- ### Section 1: Measure-to-Finite-Counting Bridge and Diagonal Extraction -/

section Bridge

/-- Ordered pairs `u < v` indexing the `\binom{n}{2}` potential edges of a graph on `Fin n`. -/
abbrev EdgeIdx (n : ℕ) : Type := {e : Fin n × Fin n // e.1 < e.2}

/-- Bijection between simple graphs on `Fin n` and Boolean assignments on `EdgeIdx n`. -/
noncomputable def graphEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ (EdgeIdx n → Bool) where
  toFun G e := decide (G.Adj e.1.1 e.1.2)
  invFun ω :=
    { Adj := fun u v =>
        (∃ h : u < v, ω ⟨(u, v), h⟩ = true) ∨ (∃ h : v < u, ω ⟨(v, u), h⟩ = true)
      symm := ⟨fun _ _ h => by
        rcases h with ⟨hlt, hw⟩ | ⟨hlt, hw⟩
        · exact Or.inr ⟨hlt, hw⟩
        · exact Or.inl ⟨hlt, hw⟩⟩
      loopless := ⟨fun u h => by
        rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl u hlt⟩ }
  left_inv G := by
    ext u v
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact of_decide_eq_true h
      · exact (of_decide_eq_true h).symm
    · intro huv
      rcases lt_trichotomy u v with hlt | rfl | hgt
      · exact Or.inl ⟨hlt, decide_eq_true huv⟩
      · exact (G.loopless.irrefl u huv).elim
      · exact Or.inr ⟨hgt, decide_eq_true huv.symm⟩
  right_inv ω := by
    funext e
    rcases e with ⟨⟨u, v⟩, huv⟩
    cases h : ω ⟨(u, v), huv⟩
    · simp only [decide_eq_false_iff_not, not_or, not_exists]
      exact ⟨fun _ h' => by rw [h] at h'; exact Bool.false_ne_true h',
        fun hgt _ => lt_asymm huv hgt⟩
    · simp only [decide_eq_true_iff]
      exact Or.inl ⟨huv, h⟩

/-- Signed adjacency entry `A(ω) u v ∈ {-1, 0, +1}` of the graph encoded by `ω`. -/
def adjSign {n : ℕ} (ω : EdgeIdx n → Bool) (u v : Fin n) : ℝ :=
  if h : u < v then (if ω ⟨(u, v), h⟩ then (1 : ℝ) else -1)
  else if h' : v < u then (if ω ⟨(v, u), h'⟩ then (1 : ℝ) else -1)
  else 0

lemma adjSign_symm {n : ℕ} (ω : EdgeIdx n → Bool) (u v : Fin n) :
    adjSign ω u v = adjSign ω v u := by
  unfold adjSign
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · have hnot : ¬ v < u := lt_asymm hlt
    simp [hlt, hnot]
  · simp
  · have hnot : ¬ u < v := lt_asymm hgt
    simp [hgt, hnot]

lemma adjSign_diag {n : ℕ} (ω : EdgeIdx n → Bool) (u : Fin n) :
    adjSign ω u u = 0 := by
  simp [adjSign]

lemma adjSign_sq_of_ne {n : ℕ} (ω : EdgeIdx n → Bool) {u v : Fin n} (h : u ≠ v) :
    (adjSign ω u v) ^ 2 = 1 := by
  unfold adjSign
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simp only [dif_pos hlt]; cases ω ⟨(u, v), hlt⟩ <;> norm_num
  · have hnot : ¬ u < v := lt_asymm hgt
    simp only [dif_neg hnot, dif_pos hgt]; cases ω ⟨(v, u), hgt⟩ <;> norm_num

lemma adjSign_eq_iff_adj {n : ℕ} (ω : EdgeIdx n → Bool) {u v : Fin n} (h : u ≠ v) :
    adjSign ω u v = if ((graphEquiv n).symm ω).Adj u v then (1 : ℝ) else -1 := by
  unfold adjSign graphEquiv
  dsimp only [Equiv.coe_fn_symm_mk]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hnot : ¬ v < u := lt_asymm hlt
    simp only [dif_pos hlt]
    cases hω : ω ⟨(u, v), hlt⟩ <;> simp [hlt, hnot, hω]
  · have hnot : ¬ u < v := lt_asymm hgt
    simp only [dif_neg hnot, dif_pos hgt]
    cases hω : ω ⟨(v, u), hgt⟩ <;> simp [hgt, hnot, hω]

/-- Exact relation between `friendliness` and the signed adjacency matrix `adjSign`. -/
lemma friendliness_eq_adjSign {n : ℕ} (ω : EdgeIdx n → Bool) (s : Finset (Fin n)) (v : Fin n) :
    let σ : Fin n → ℝ := fun u => if u ∈ s then (1 : ℝ) else -1
    (2 : ℝ) * (Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ) =
      σ v * (∑ w : Fin n, adjSign ω v w * σ w) +
        σ v * (∑ w : Fin n, σ w) - 1 := by
  intro σ
  let G := (graphEquiv n).symm ω
  have h1 : ∀ w : Fin n, w ≠ v →
      (if G.Adj v w ∧ (w ∈ s ↔ v ∈ s) then (2 : ℝ) else 0) -
      (if G.Adj v w ∧ ¬ (w ∈ s ↔ v ∈ s) then (2 : ℝ) else 0) =
      σ v * (adjSign ω v w * σ w) + σ v * σ w := by
    intro w hne
    rw [adjSign_eq_iff_adj ω hne.symm]
    by_cases hadj : G.Adj v w <;> by_cases hvs : v ∈ s <;> by_cases hws : w ∈ s <;>
      simp [σ, G, hadj, hvs, hws] <;> ring
  have hL : (2 : ℝ) * (Green91.friendliness G s v : ℝ) =
      ∑ w : Fin n, ((if G.Adj v w ∧ (w ∈ s ↔ v ∈ s) then (2 : ℝ) else 0) -
        (if G.Adj v w ∧ ¬ (w ∈ s ↔ v ∈ s) then (2 : ℝ) else 0)) := by
    unfold Green91.friendliness
    push_cast
    rw [Finset.sum_sub_distrib, Finset.card_filter, Finset.card_filter]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
  have hR : σ v * (∑ w : Fin n, adjSign ω v w * σ w) + σ v * (∑ w : Fin n, σ w) - 1 =
      ∑ w : Fin n, if w = v then (0 : ℝ) else (σ v * (adjSign ω v w * σ w) + σ v * σ w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hdiag : σ v * (adjSign ω v v * σ v) + σ v * σ v = 1 := by
      rw [adjSign_diag]; by_cases h : v ∈ s <;> simp [σ, h]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun w => σ v * (adjSign ω v w * σ w) + σ v * σ w) (Finset.mem_univ v)
    have hsplit2 := Finset.add_sum_erase Finset.univ
      (fun w => if w = v then (0 : ℝ) else (σ v * (adjSign ω v w * σ w) + σ v * σ w))
      (Finset.mem_univ v)
    simp only [ite_true, zero_add] at hsplit2
    have heq : ∑ x ∈ Finset.univ.erase v,
        (if x = v then (0 : ℝ) else (σ v * (adjSign ω v x * σ x) + σ v * σ x)) =
        ∑ x ∈ Finset.univ.erase v, (σ v * (adjSign ω v x * σ x) + σ v * σ x) :=
      Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
    linarith [hsplit, hsplit2, heq, hdiag]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hwv : w = v
  · subst hwv
    have hno : ¬ G.Adj w w := G.loopless.irrefl w
    simp only [hno, false_and, ite_false, sub_self, ite_true]
  · rw [if_neg hwv, h1 w hwv]

/-- `Green91.prob n P` equals the uniform fraction of Boolean edge assignments satisfying `P`. -/
lemma prob_eq_card_div (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    Green91.prob n P =
      ((Finset.univ.filter (fun ω : EdgeIdx n → Bool => P ((graphEquiv n).symm ω))).card : ENNReal) /
        (Fintype.card (EdgeIdx n → Bool) : ENNReal) := by
  let p : unitInterval := ⟨1 / 2, by norm_num⟩
  let μ := SimpleGraph.binomialRandom (Fin n) p
  let c : ENNReal := (unitInterval.toNNReal p : ENNReal) ^ (n.choose 2)
  have hsingle : ∀ G : SimpleGraph (Fin n), μ {G} = c := by
    intro G
    have h := SimpleGraph.binomialRandom_singleton (V := Fin n) p G
    have hp : unitInterval.symm p = p := by
      ext; simp [p, unitInterval.symm]; norm_num
    have hle : G.edgeSet.ncard ≤ (Nat.card (Fin n)).choose 2 := by
      have hcard : Nat.card (Fin n) = n := Nat.card_fin n
      have h1 : G.edgeSet.ncard ≤ (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_compl_diagSet G) (Set.toFinite _)
      have h2 : (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).ncard = n.choose 2 := by
        rw [← Nat.card_coe_set_eq, ← Fintype.card_eq_nat_card, Sym2.card_diagSet_compl,
          Fintype.card_fin]
      rw [hcard]; exact h1.trans h2.le
    rw [hp, ← pow_add, Nat.add_sub_of_le hle, Nat.card_fin] at h
    exact h
  have hmeas_finset : ∀ S : Finset (SimpleGraph (Fin n)),
      μ (S : Set (SimpleGraph (Fin n))) = (S.card : ENNReal) * c := by
    intro S
    have hbi : (S : Set (SimpleGraph (Fin n))) = ⋃ G ∈ S, ({G} : Set (SimpleGraph (Fin n))) := by
      ext G; simp
    rw [hbi, MeasureTheory.measure_biUnion_finset]
    · simp only [hsingle, Finset.sum_const, nsmul_eq_mul]
    · intro G₁ _ G₂ _ hne; exact Set.disjoint_singleton.mpr hne
    · intro G _
      have heq : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
        ext H; simp
      rw [heq]
      exact SimpleGraph.measurable_adj (MeasurableSet.singleton G.Adj)
  have huniv : (Fintype.card (SimpleGraph (Fin n)) : ENNReal) * c = 1 := by
    have h1 := hmeas_finset Finset.univ
    rw [Finset.coe_univ, measure_univ, Finset.card_univ] at h1
    exact h1.symm
  have hpos_card : (Fintype.card (SimpleGraph (Fin n)) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := SimpleGraph (Fin n))).ne'
  have hne_top : (Fintype.card (SimpleGraph (Fin n)) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpow_eq : c = (Fintype.card (SimpleGraph (Fin n)) : ENNReal)⁻¹ := by
    calc c = 1 * c := (one_mul c).symm
      _ = ((Fintype.card (SimpleGraph (Fin n)) : ENNReal)⁻¹ *
            (Fintype.card (SimpleGraph (Fin n)) : ENNReal)) * c := by
          rw [ENNReal.inv_mul_cancel hpos_card hne_top]
      _ = (Fintype.card (SimpleGraph (Fin n)) : ENNReal)⁻¹ *
            ((Fintype.card (SimpleGraph (Fin n)) : ENNReal) * c) := mul_assoc _ _ _
      _ = (Fintype.card (SimpleGraph (Fin n)) : ENNReal)⁻¹ := by rw [huniv, mul_one]
  let S : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (fun G => P G)
  have hset : {G : SimpleGraph (Fin n) | P G} = (S : Set (SimpleGraph (Fin n))) := by
    ext G; simp [S]
  have hcard_eq : S.card =
      (Finset.univ.filter (fun ω : EdgeIdx n → Bool => P ((graphEquiv n).symm ω))).card := by
    refine Finset.card_bij (fun G _ => graphEquiv n G) ?_ ?_ ?_
    · intro G hG
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
      simpa using hG
    · intro G₁ _ G₂ _ h; exact (graphEquiv n).injective h
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact ⟨(graphEquiv n).symm ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩,
        (graphEquiv n).apply_symm_apply ω⟩
  have htot_eq : Fintype.card (SimpleGraph (Fin n)) = Fintype.card (EdgeIdx n → Bool) :=
    Fintype.card_congr (graphEquiv n)
  change μ {G | P G} = _
  rw [hset, hmeas_finset S, hpow_eq, hcard_eq, htot_eq, div_eq_mul_inv]

/-- Convert a real failure-probability upper bound `≤ r` on Boolean cubes to `1 - ofReal r ≤ prob n P`. -/
lemma prob_ge_of_fail_card_le {n : ℕ} {P : SimpleGraph (Fin n) → Prop} {r : ℝ} (hr0 : 0 ≤ r)
    (hfail : ((Finset.univ.filter (fun ω : EdgeIdx n → Bool => ¬ P ((graphEquiv n).symm ω))).card : ℝ) ≤
      r * (Fintype.card (EdgeIdx n → Bool) : ℝ)) :
    1 - ENNReal.ofReal r ≤ Green91.prob n P := by
  rw [prob_eq_card_div]
  set N := Fintype.card (EdgeIdx n → Bool)
  set G_cnt := (Finset.univ.filter (fun ω : EdgeIdx n → Bool => P ((graphEquiv n).symm ω))).card
  set B_cnt := (Finset.univ.filter (fun ω : EdgeIdx n → Bool => ¬ P ((graphEquiv n).symm ω))).card
  have hsum : G_cnt + B_cnt = N := by
    simpa only [G_cnt, B_cnt, N, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (EdgeIdx n → Bool)))
        (p := fun ω => P ((graphEquiv n).symm ω))
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hreal : 1 - r ≤ (G_cnt : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos]
    have hsumR : (G_cnt : ℝ) + (B_cnt : ℝ) = (N : ℝ) := by exact_mod_cast hsum
    linarith [hfail, hsumR]
  have hENN : ENNReal.ofReal (1 - r) ≤ ENNReal.ofReal ((G_cnt : ℝ) / (N : ℝ)) :=
    ENNReal.ofReal_le_ofReal hreal
  have hLHS : 1 - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
    rw [ENNReal.ofReal_sub 1 hr0, ENNReal.ofReal_one]
  have hRHS : ENNReal.ofReal ((G_cnt : ℝ) / (N : ℝ)) = (G_cnt : ENNReal) / (N : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos hNpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hLHS, ← hRHS]
  exact hENN

/-- Diagonal extraction from fixed-tolerance `1 / (k + 1)` convergence to `f = o(n)`. -/
lemma diag_extract (P : ℕ → ℕ → ENNReal) (hP : ∀ k, Tendsto (P k) atTop (𝓝 1)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ Tendsto (fun n => P (k n) n) atTop (𝓝 1) := by
  choose N hN using fun k => eventually_atTop.mp
    ((ENNReal.tendsto_nhds ENNReal.one_ne_top).mp (hP k) ((k : ENNReal)⁻¹)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k)))
  let M (k : ℕ) := N k + k
  let kk (n : ℕ) := Nat.findGreatest (fun k => M k ≤ n) n
  have hkk_ge {K n : ℕ} (h : M K ≤ n) : K ≤ kk n :=
    Nat.le_findGreatest ((Nat.le_add_left K (N K)).trans h) h
  refine ⟨kk, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    exact fun K => ⟨M K, fun _ hn => hkk_ge hn⟩
  · rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
    intro ε hε
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    filter_upwards [eventually_ge_atTop (M K)] with n hn
    have hKn : K ≤ n := (Nat.le_add_left K (N K)).trans hn
    have hk : M (kk n) ≤ n :=
      Nat.findGreatest_spec (P := fun k => M k ≤ n) hKn hn
    have hin := hN (kk n) n ((Nat.le_add_right _ _).trans hk)
    have hεle : ((kk n : ENNReal))⁻¹ ≤ ε :=
      (ENNReal.inv_le_inv.mpr (by exact_mod_cast hkk_ge hn)).trans hK.le
    exact ⟨(tsub_le_tsub_left hεle 1).trans hin.1, hin.2.trans (add_le_add_right hεle 1)⟩

end Bridge

/- ### Section 2: Finite Probability Toolkit (Hoeffding, Central Binomial, Efron–Stein) -/

section FiniteProb

/-- Elementary inequality `cosh(x) ≤ exp(x^2 / 2)`. -/
lemma cosh_le_exp_sq_div_two (x : ℝ) :
    (Real.exp x + Real.exp (-x)) / 2 ≤ Real.exp (x ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq x
  rwa [Real.cosh_eq] at h

/-- Product MGF for a weighted Rademacher sum over `Fin N → Bool`. -/
lemma rademacher_mgf_fin (θ : ℝ) :
    ∀ (N : ℕ) (c : Fin N → ℝ),
      (∑ ω : Fin N → Bool, Real.exp (θ * ∑ i : Fin N, if ω i then c i else -c i)) ≤
        Real.exp (θ ^ 2 / 2 * ∑ i : Fin N, (c i) ^ 2) * (2 ^ N : ℝ)
  | 0, _ => by simp
  | N + 1, c => by
    let e : (Fin (N + 1) → Bool) ≃ Bool × (Fin N → Bool) :=
      ⟨fun ω => (ω 0, fun i => ω i.succ),
       fun p => Fin.cons (α := fun _ => Bool) p.1 p.2,
       fun ω => by funext i; refine Fin.cases rfl (fun _ => rfl) i,
       fun ⟨b, τ⟩ => by ext <;> simp⟩
    have hsplit :
        ∑ ω : Fin (N + 1) → Bool, Real.exp (θ * ∑ i : Fin (N + 1), if ω i then c i else -c i) =
        (Real.exp (θ * c 0) + Real.exp (-(θ * c 0))) *
          ∑ τ : Fin N → Bool, Real.exp (θ * ∑ i : Fin N, if τ i then c i.succ else -c i.succ) := by
      rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, e, Equiv.coe_fn_symm_mk]
      have hT : ∀ τ : Fin N → Bool,
          Real.exp (θ * ∑ i : Fin (N + 1), if (Fin.cons (α := fun _ => Bool) true τ) i then c i else -c i) =
          Real.exp (θ * c 0) * Real.exp (θ * ∑ i : Fin N, if τ i then c i.succ else -c i.succ) := by
        intro τ; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ, ite_true]
        rw [mul_add, Real.exp_add]
      have hF : ∀ τ : Fin N → Bool,
          Real.exp (θ * ∑ i : Fin (N + 1), if (Fin.cons (α := fun _ => Bool) false τ) i then c i else -c i) =
          Real.exp (-(θ * c 0)) * Real.exp (θ * ∑ i : Fin N, if τ i then c i.succ else -c i.succ) := by
        intro τ; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ite_false]
        rw [mul_add, Real.exp_add]; congr 2; ring
      simp_rw [hT, hF]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_mul]
    rw [hsplit]
    have h0 : Real.exp (θ * c 0) + Real.exp (-(θ * c 0)) ≤
        Real.exp (θ ^ 2 / 2 * (c 0) ^ 2) * 2 := by
      have hc := cosh_le_exp_sq_div_two (θ * c 0)
      have hsq : (θ * c 0) ^ 2 / 2 = θ ^ 2 / 2 * (c 0) ^ 2 := by ring
      rw [hsq] at hc
      linarith
    have ih := rademacher_mgf_fin θ N (fun i => c i.succ)
    have hsum_nn : 0 ≤ ∑ τ : Fin N → Bool,
        Real.exp (θ * ∑ i : Fin N, if τ i then c i.succ else -c i.succ) :=
      Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    calc (Real.exp (θ * c 0) + Real.exp (-(θ * c 0))) *
          ∑ τ : Fin N → Bool, Real.exp (θ * ∑ i : Fin N, if τ i then c i.succ else -c i.succ)
        ≤ (Real.exp (θ ^ 2 / 2 * (c 0) ^ 2) * 2) *
            (Real.exp (θ ^ 2 / 2 * ∑ i : Fin N, (c i.succ) ^ 2) * (2 ^ N : ℝ)) :=
          mul_le_mul h0 ih hsum_nn (by positivity)
      _ = (Real.exp (θ ^ 2 / 2 * (c 0) ^ 2) * Real.exp (θ ^ 2 / 2 * ∑ i : Fin N, (c i.succ) ^ 2)) *
            (2 ^ (N + 1) : ℝ) := by rw [pow_succ]; ring
      _ = Real.exp (θ ^ 2 / 2 * ∑ i : Fin (N + 1), (c i) ^ 2) * (2 ^ (N + 1) : ℝ) := by
          rw [← Real.exp_add, Fin.sum_univ_succ, mul_add]

/-- Two-sided Rademacher Hoeffding inequality on any finite Boolean cube `X → Bool`. -/
theorem rademacher_hoeffding {X : Type*} [Fintype X] [DecidableEq X]
    (c : X → ℝ) (V t : ℝ) (hV : 0 < V) (ht : 0 ≤ t)
    (hV_ge : ∑ x : X, (c x) ^ 2 ≤ V) :
    ((Finset.univ.filter (fun ω : X → Bool =>
      t ≤ |∑ x : X, if ω x then c x else -c x|)).card : ℝ) ≤
      2 * Real.exp (-t ^ 2 / (2 * V)) * (Fintype.card (X → Bool) : ℝ) := by
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let eAll : (X → Bool) ≃ (Fin (Fintype.card X) → Bool) :=
    Equiv.arrowCongr eX (Equiv.refl Bool)
  have hcard : (Fintype.card (X → Bool) : ℝ) = (2 ^ Fintype.card X : ℝ) := by
    simp
  have hone : ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ((Finset.univ.filter (fun ω : X → Bool =>
        t ≤ sgn * ∑ x : X, if ω x then c x else -c x)).card : ℝ) ≤
        Real.exp (-t ^ 2 / (2 * V)) * (Fintype.card (X → Bool) : ℝ) := by
    intro sgn hsgn
    let θ : ℝ := t / V
    have hθ0 : 0 ≤ θ := div_nonneg ht hV.le
    have hmgf : ∑ ω : X → Bool,
        Real.exp ((sgn * θ) * ∑ x : X, if ω x then c x else -c x) ≤
        Real.exp (θ ^ 2 / 2 * V) * (Fintype.card (X → Bool) : ℝ) := by
      have hcomp := rademacher_mgf_fin (sgn * θ) (Fintype.card X) (c ∘ eX.symm)
      have hsum_eq : ∑ ω : X → Bool, Real.exp ((sgn * θ) * ∑ x : X, if ω x then c x else -c x) =
          ∑ τ : Fin (Fintype.card X) → Bool,
            Real.exp ((sgn * θ) * ∑ i : Fin (Fintype.card X), if τ i then c (eX.symm i) else -c (eX.symm i)) := by
        rw [← Equiv.sum_comp eAll.symm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        congr 2
        rw [← Equiv.sum_comp eX.symm]
        refine Finset.sum_congr rfl fun i _ => by simp [eAll]
      have hsq_eq : ∑ i : Fin (Fintype.card X), (c (eX.symm i)) ^ 2 = ∑ x : X, (c x) ^ 2 :=
        Equiv.sum_comp eX.symm (fun x => (c x) ^ 2)
      have hsgn_sq : (sgn * θ) ^ 2 = θ ^ 2 := by rcases hsgn with rfl | rfl <;> ring
      rw [hsum_eq, hcard]
      refine hcomp.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity))
      change (sgn * θ) ^ 2 / 2 * ∑ i : Fin (Fintype.card X), (c (eX.symm i)) ^ 2 ≤ _
      rw [hsgn_sq, hsq_eq]
      exact mul_le_mul_of_nonneg_left hV_ge (by positivity)
    have hmarkov : Real.exp (θ * t) *
        ((Finset.univ.filter (fun ω : X → Bool =>
          t ≤ sgn * ∑ x : X, if ω x then c x else -c x)).card : ℝ) ≤
        ∑ ω : X → Bool, Real.exp ((sgn * θ) * ∑ x : X, if ω x then c x else -c x) := by
      calc Real.exp (θ * t) *
            ((Finset.univ.filter (fun ω : X → Bool =>
              t ≤ sgn * ∑ x : X, if ω x then c x else -c x)).card : ℝ)
          = ∑ _ω ∈ Finset.univ.filter (fun ω : X → Bool =>
              t ≤ sgn * ∑ x : X, if ω x then c x else -c x), Real.exp (θ * t) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : X → Bool =>
              t ≤ sgn * ∑ x : X, if ω x then c x else -c x),
              Real.exp ((sgn * θ) * ∑ x : X, if ω x then c x else -c x) := by
            refine Finset.sum_le_sum fun ω hω => Real.exp_le_exp.mpr ?_
            have hle := (Finset.mem_filter.mp hω).2
            calc θ * t ≤ θ * (sgn * ∑ x : X, if ω x then c x else -c x) :=
                  mul_le_mul_of_nonneg_left hle hθ0
              _ = (sgn * θ) * ∑ x : X, if ω x then c x else -c x := by ring
        _ ≤ ∑ ω : X → Bool, Real.exp ((sgn * θ) * ∑ x : X, if ω x then c x else -c x) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
    have hcomb := (le_div_iff₀' (Real.exp_pos (θ * t))).mpr (hmarkov.trans hmgf)
    have hexp_eq : θ ^ 2 / 2 * V - θ * t = -t ^ 2 / (2 * V) := by
      simp only [θ]; field_simp; ring
    calc ((Finset.univ.filter (fun ω : X → Bool =>
            t ≤ sgn * ∑ x : X, if ω x then c x else -c x)).card : ℝ)
        ≤ Real.exp (θ ^ 2 / 2 * V) * (Fintype.card (X → Bool) : ℝ) / Real.exp (θ * t) := hcomb
      _ = Real.exp (θ ^ 2 / 2 * V - θ * t) * (Fintype.card (X → Bool) : ℝ) := by
          rw [mul_div_right_comm, ← Real.exp_sub]
      _ = Real.exp (-t ^ 2 / (2 * V)) * (Fintype.card (X → Bool) : ℝ) := by rw [hexp_eq]
  have hcov : Finset.univ.filter (fun ω : X → Bool =>
      t ≤ |∑ x : X, if ω x then c x else -c x|) ⊆
      Finset.univ.filter (fun ω : X → Bool => t ≤ (1 : ℝ) * ∑ x : X, if ω x then c x else -c x) ∪
      Finset.univ.filter (fun ω : X → Bool => t ≤ (-1 : ℝ) * ∑ x : X, if ω x then c x else -c x) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
    rcases le_or_gt 0 (∑ x : X, if ω x then c x else -c x) with hnn | hneg
    · left; rw [abs_of_nonneg hnn] at hω; linarith
    · right; rw [abs_of_neg hneg] at hω; linarith
  have hcu : ((Finset.univ.filter (fun ω : X → Bool =>
      t ≤ |∑ x : X, if ω x then c x else -c x|)).card : ℝ) ≤
      ((Finset.univ.filter (fun ω : X → Bool =>
        t ≤ (1 : ℝ) * ∑ x : X, if ω x then c x else -c x)).card : ℝ) +
      ((Finset.univ.filter (fun ω : X → Bool =>
        t ≤ (-1 : ℝ) * ∑ x : X, if ω x then c x else -c x)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  linarith [hcu, hone 1 (Or.inl rfl), hone (-1) (Or.inr rfl)]

/-- Central binomial bound `((2r choose r) / 2^(2r))^2 ≤ 1 / (2r + 1)`. -/
lemma central_binom_sq_le :
    ∀ r : ℕ, (((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ)) ^ 2 ≤ 1 / (2 * (r : ℝ) + 1)
  | 0 => by norm_num
  | r + 1 => by
    have ih := central_binom_sq_le r
    have hrec : ((2 * (r + 1)).choose (r + 1) : ℝ) * ((r + 1 : ℝ)) =
        ((2 * r + 1 : ℝ) * 2) * ((2 * r).choose r : ℝ) := by
      have hf1 := Nat.choose_mul_factorial_mul_factorial (show r + 1 ≤ 2 * (r + 1) by omega)
      have hf0 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
      rw [show 2 * (r + 1) - (r + 1) = r + 1 by omega] at hf1
      rw [show 2 * r - r = r by omega] at hf0
      have hfac : (2 * (r + 1)).factorial = (2 * r + 2) * (2 * r + 1) * (2 * r).factorial := by
        rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
        ring
      have hfr : (r + 1).factorial = (r + 1) * r.factorial := Nat.factorial_succ r
      have hmul : (2 * (r + 1)).choose (r + 1) * (r + 1) * (r + 1) * (r.factorial * r.factorial) =
          (2 * r + 2) * (2 * r + 1) * (2 * r).choose r * (r.factorial * r.factorial) := by
        calc (2 * (r + 1)).choose (r + 1) * (r + 1) * (r + 1) * (r.factorial * r.factorial)
            = (2 * (r + 1)).choose (r + 1) * (r + 1).factorial * (r + 1).factorial := by rw [hfr]; ring
          _ = (2 * (r + 1)).factorial := hf1
          _ = (2 * r + 2) * (2 * r + 1) * (2 * r).factorial := hfac
          _ = (2 * r + 2) * (2 * r + 1) * ((2 * r).choose r * r.factorial * r.factorial) := by rw [← hf0]
          _ = (2 * r + 2) * (2 * r + 1) * (2 * r).choose r * (r.factorial * r.factorial) := by ring
      have hpos_f : 0 < r.factorial * r.factorial := Nat.mul_pos (Nat.factorial_pos r) (Nat.factorial_pos r)
      have hnat : (2 * (r + 1)).choose (r + 1) * (r + 1) * (r + 1) =
          (2 * r + 2) * (2 * r + 1) * (2 * r).choose r :=
        Nat.eq_of_mul_eq_mul_right hpos_f hmul
      have hreal : ((2 * (r + 1)).choose (r + 1) : ℝ) * ((r : ℝ) + 1) * ((r : ℝ) + 1) =
          (2 * (r : ℝ) + 2) * (2 * (r : ℝ) + 1) * ((2 * r).choose r : ℝ) := by
        exact_mod_cast hnat
      have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      have hfac2 : (2 * (r : ℝ) + 2) = 2 * ((r : ℝ) + 1) := by ring
      rw [hfac2] at hreal
      nlinarith only [hreal, hr1]
    have hrat : ((2 * (r + 1)).choose (r + 1) : ℝ) / (2 ^ (2 * (r + 1)) : ℝ) =
        ((2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2)) *
          (((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ)) := by
      have h2p : (2 ^ (2 * (r + 1)) : ℝ) = 4 * (2 ^ (2 * r) : ℝ) := by
        rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]; norm_num; ring
      rw [h2p]
      have hpos1 : (0 : ℝ) < (2 ^ (2 * r) : ℝ) := by positivity
      have hpos2 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      field_simp
      linarith [hrec]
    rw [hrat, mul_pow]
    have hstep_le : ((2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2)) ^ 2 * (1 / (2 * (r : ℝ) + 1)) ≤
        1 / (2 * ((r + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (r : ℝ)]
    exact (mul_le_mul_of_nonneg_left ih (sq_nonneg _)).trans hstep_le

/-- Universal anti-concentration bound `(m.choose k) / 2^m ≤ 2 / √(m + 1)`. -/
lemma choose_div_two_pow_le (m k : ℕ) :
    (m.choose k : ℝ) / (2 ^ m : ℝ) ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
  have hmax : m.choose k ≤ m.choose (m / 2) := Nat.choose_le_middle k m
  have hmid : (m.choose (m / 2) : ℝ) / (2 ^ m : ℝ) ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr
      have hhalf : (r + r) / 2 = r := by omega
      rw [hhalf, show r + r = 2 * r by omega]
      have hsq := central_binom_sq_le r
      have hsqrt : ((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ) ≤ 1 / Real.sqrt (2 * (r : ℝ) + 1) := by
        have h1 : (((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ)) ^ 2 ≤
            (1 / Real.sqrt (2 * (r : ℝ) + 1)) ^ 2 := by
          have hr : (1 / Real.sqrt (2 * (r : ℝ) + 1)) ^ 2 = 1 / (2 * (r : ℝ) + 1) := by
            rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
          rw [hr]; exact hsq
        nlinarith [h1, div_nonneg (Nat.cast_nonneg ((2 * r).choose r)) (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r)),
          div_nonneg zero_le_one (Real.sqrt_nonneg (2 * (r : ℝ) + 1))]
      have hcast : ((2 * r : ℕ) : ℝ) + 1 = 2 * (r : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have h12 : (1 : ℝ) / Real.sqrt (2 * (r : ℝ) + 1) ≤ 2 / Real.sqrt (2 * (r : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
      exact hsqrt.trans h12
    · subst hr
      have hhalf : (2 * r + 1) / 2 = r := by omega
      rw [hhalf]
      have hle2 : (2 * r + 1).choose r ≤ 2 * (2 * r).choose r := by
        rcases r with _ | r
        · decide
        · have h1 := Nat.choose_succ_succ (2 * (r + 1)) r
          have h2 : (2 * (r + 1)).choose r ≤ (2 * (r + 1)).choose (r + 1) := by
            have := Nat.choose_le_middle r (2 * (r + 1))
            simpa [show (2 * (r + 1)) / 2 = r + 1 by omega] using this
          have h3 : (2 * (r + 1) + 1).choose (r + 1) = (2 * (r + 1)).choose r + (2 * (r + 1)).choose (r + 1) := by
            simpa [Nat.add_comm] using h1
          omega
      have hsq := central_binom_sq_le r
      have hsqrt : ((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ) ≤ 1 / Real.sqrt (2 * (r : ℝ) + 1) := by
        have h1 : (((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ)) ^ 2 ≤
            (1 / Real.sqrt (2 * (r : ℝ) + 1)) ^ 2 := by
          have hr : (1 / Real.sqrt (2 * (r : ℝ) + 1)) ^ 2 = 1 / (2 * (r : ℝ) + 1) := by
            rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
          rw [hr]; exact hsq
        nlinarith [h1, div_nonneg (Nat.cast_nonneg ((2 * r).choose r)) (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r)),
          div_nonneg zero_le_one (Real.sqrt_nonneg (2 * (r : ℝ) + 1))]
      have hle_div : ((2 * r + 1).choose r : ℝ) / (2 ^ (2 * r + 1) : ℝ) ≤
          ((2 * r).choose r : ℝ) / (2 ^ (2 * r) : ℝ) := by
        rw [pow_succ, show (2 ^ (2 * r) : ℝ) * 2 = 2 * (2 ^ (2 * r) : ℝ) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hle2R : ((2 * r + 1).choose r : ℝ) ≤ 2 * ((2 * r).choose r : ℝ) := by exact_mod_cast hle2
        nlinarith [hle2R, show (0 : ℝ) < (2 ^ (2 * r) : ℝ) by positivity]
      have hsqrt_cmp : 1 / Real.sqrt (2 * (r : ℝ) + 1) ≤ 2 / Real.sqrt (((2 * r + 1 : ℕ) : ℝ) + 1) := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))]
        have hsq' : (Real.sqrt (((2 * r + 1 : ℕ) : ℝ) + 1)) ^ 2 ≤
            (2 * Real.sqrt (2 * (r : ℝ) + 1)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
          push_cast; linarith
        nlinarith [hsq', Real.sqrt_nonneg (((2 * r + 1 : ℕ) : ℝ) + 1),
          Real.sqrt_nonneg (2 * (r : ℝ) + 1)]
      exact (hle_div.trans hsqrt).trans hsqrt_cmp
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hmax) (by positivity)).trans hmid

/-- Uniform-cube Efron–Stein variance inequality on `Fin N → Bool`. -/
lemma efron_stein_fin :
    ∀ (N : ℕ) (f : (Fin N → Bool) → ℝ),
      let μ : ℝ := (∑ ω : Fin N → Bool, f ω) / (2 ^ N : ℝ)
      (∑ ω : Fin N → Bool, (f ω - μ) ^ 2) / (2 ^ N : ℝ) ≤
        (1 / 4) * ∑ i : Fin N,
          (∑ ω : Fin N → Bool, (f ω - f (Function.update ω i (!ω i))) ^ 2) / (2 ^ N : ℝ)
  | 0, f => by
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, div_one,
      Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    simp
  | N + 1, f => by
    intro μ
    let e : (Fin (N + 1) → Bool) ≃ Bool × (Fin N → Bool) :=
      ⟨fun ω => (ω 0, fun i => ω i.succ),
       fun p => Fin.cons (α := fun _ => Bool) p.1 p.2,
       fun ω => by funext i; refine Fin.cases rfl (fun _ => rfl) i,
       fun ⟨b, τ⟩ => by ext <;> simp⟩
    let gT : (Fin N → Bool) → ℝ := fun τ => f (Fin.cons (α := fun _ => Bool) true τ)
    let gF : (Fin N → Bool) → ℝ := fun τ => f (Fin.cons (α := fun _ => Bool) false τ)
    let gBar : (Fin N → Bool) → ℝ := fun τ => (gT τ + gF τ) / 2
    have h2pos : (0 : ℝ) < (2 ^ N : ℝ) := by positivity
    have hμ_eq : μ = (∑ τ : Fin N → Bool, gBar τ) / (2 ^ N : ℝ) := by
      have hsum : ∑ ω : Fin (N + 1) → Bool, f ω =
          ∑ τ : Fin N → Bool, (gT τ + gF τ) := by
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, e, Equiv.coe_fn_symm_mk, Finset.sum_add_distrib, gT, gF]
      simp only [μ, hsum, pow_succ, gBar]
      rw [← Finset.sum_div]
      field_simp
    have hdecomp : (∑ ω : Fin (N + 1) → Bool, (f ω - μ) ^ 2) / (2 ^ (N + 1) : ℝ) =
        (∑ τ : Fin N → Bool, (gBar τ - μ) ^ 2) / (2 ^ N : ℝ) +
        (1 / 4) * ((∑ ω : Fin (N + 1) → Bool,
          (f ω - f (Function.update ω 0 (!ω 0))) ^ 2) / (2 ^ (N + 1) : ℝ)) := by
      have hL : ∑ ω : Fin (N + 1) → Bool, (f ω - μ) ^ 2 =
          ∑ τ : Fin N → Bool, ((gT τ - μ) ^ 2 + (gF τ - μ) ^ 2) := by
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, e, Equiv.coe_fn_symm_mk, Finset.sum_add_distrib, gT, gF]
      have h0 : ∑ ω : Fin (N + 1) → Bool, (f ω - f (Function.update ω 0 (!ω 0))) ^ 2 =
          ∑ τ : Fin N → Bool, (2 * (gT τ - gF τ) ^ 2) := by
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, e, Equiv.coe_fn_symm_mk, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        have hT0 : Function.update (Fin.cons (α := fun _ => Bool) true τ) 0
            (!Fin.cons (α := fun _ => Bool) true τ 0) = Fin.cons (α := fun _ => Bool) false τ := by
          funext i; refine Fin.cases (by simp) (fun j => by simp) i
        have hF0 : Function.update (Fin.cons (α := fun _ => Bool) false τ) 0
            (!Fin.cons (α := fun _ => Bool) false τ 0) = Fin.cons (α := fun _ => Bool) true τ := by
          funext i; refine Fin.cases (by simp) (fun j => by simp) i
        rw [hT0, hF0]
        simp only [gT, gF]; ring
      have hpw : ∀ τ : Fin N → Bool,
          (gT τ - μ) ^ 2 + (gF τ - μ) ^ 2 = 2 * (gBar τ - μ) ^ 2 + (1 / 2) * (gT τ - gF τ) ^ 2 := by
        intro τ; simp only [gBar]; ring
      rw [hL, h0]
      simp_rw [hpw]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, pow_succ]
      field_simp; ring
    have ih := efron_stein_fin N gBar
    rw [← hμ_eq] at ih
    have hsucc : ∀ j : Fin N,
        (∑ τ : Fin N → Bool, (gBar τ - gBar (Function.update τ j (!τ j))) ^ 2) / (2 ^ N : ℝ) ≤
        (∑ ω : Fin (N + 1) → Bool, (f ω - f (Function.update ω j.succ (!ω j.succ))) ^ 2) /
          (2 ^ (N + 1) : ℝ) := by
      intro j
      have hR : ∑ ω : Fin (N + 1) → Bool, (f ω - f (Function.update ω j.succ (!ω j.succ))) ^ 2 =
          ∑ τ : Fin N → Bool, ((gT τ - gT (Function.update τ j (!τ j))) ^ 2 +
            (gF τ - gF (Function.update τ j (!τ j))) ^ 2) := by
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, e, Equiv.coe_fn_symm_mk, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        have hTj : Function.update (Fin.cons (α := fun _ => Bool) true τ) j.succ
            (!Fin.cons (α := fun _ => Bool) true τ j.succ) =
            Fin.cons (α := fun _ => Bool) true (Function.update τ j (!τ j)) := by
          funext i
          refine Fin.cases (by simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]) (fun k => ?_) i
          by_cases hkj : k = j
          · subst hkj; simp
          · simp [hkj]
        have hFj : Function.update (Fin.cons (α := fun _ => Bool) false τ) j.succ
            (!Fin.cons (α := fun _ => Bool) false τ j.succ) =
            Fin.cons (α := fun _ => Bool) false (Function.update τ j (!τ j)) := by
          funext i
          refine Fin.cases (by simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]) (fun k => ?_) i
          by_cases hkj : k = j
          · subst hkj; simp
          · simp [hkj]
        rw [hTj, hFj]
      rw [hR, pow_succ, div_le_div_iff₀ h2pos (by positivity)]
      have hpw : ∀ τ : Fin N → Bool,
          (gBar τ - gBar (Function.update τ j (!τ j))) ^ 2 * 2 ≤
            (gT τ - gT (Function.update τ j (!τ j))) ^ 2 +
            (gF τ - gF (Function.update τ j (!τ j))) ^ 2 := by
        intro τ
        simp only [gBar]
        nlinarith [sq_nonneg ((gT τ - gT (Function.update τ j (!τ j))) -
          (gF τ - gF (Function.update τ j (!τ j))))]
      have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hpw τ
      rw [← Finset.sum_mul] at hsum
      have := mul_le_mul_of_nonneg_right hsum h2pos.le
      linarith
    rw [hdecomp, Fin.sum_univ_succ, mul_add]
    have hsum_le : ∑ j : Fin N,
        (∑ τ : Fin N → Bool, (gBar τ - gBar (Function.update τ j (!τ j))) ^ 2) / (2 ^ N : ℝ) ≤
        ∑ j : Fin N,
          (∑ ω : Fin (N + 1) → Bool, (f ω - f (Function.update ω j.succ (!ω j.succ))) ^ 2) /
            (2 ^ (N + 1) : ℝ) :=
      Finset.sum_le_sum fun j _ => hsucc j
    linarith [ih, hsum_le]

/-- Efron–Stein variance inequality on an arbitrary finite Boolean cube `X → Bool`. -/
theorem efron_stein_bool {X : Type*} [Fintype X] [DecidableEq X] (f : (X → Bool) → ℝ) :
    let μ : ℝ := (∑ ω : X → Bool, f ω) / (Fintype.card (X → Bool) : ℝ)
    (∑ ω : X → Bool, (f ω - μ) ^ 2) / (Fintype.card (X → Bool) : ℝ) ≤
      (1 / 4) * ∑ x : X,
        (∑ ω : X → Bool, (f ω - f (Function.update ω x (!ω x))) ^ 2) /
          (Fintype.card (X → Bool) : ℝ) := by
  intro μ
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let eAll : (X → Bool) ≃ (Fin (Fintype.card X) → Bool) :=
    Equiv.arrowCongr eX (Equiv.refl Bool)
  have hcard : (Fintype.card (X → Bool) : ℝ) = (2 ^ Fintype.card X : ℝ) := by simp
  let g : (Fin (Fintype.card X) → Bool) → ℝ := fun τ => f (eAll.symm τ)
  have hμ_eq : μ = (∑ τ : Fin (Fintype.card X) → Bool, g τ) / (2 ^ Fintype.card X : ℝ) := by
    simp only [μ, hcard, g]; rw [Equiv.sum_comp eAll.symm]
  have hL : (∑ ω : X → Bool, (f ω - μ) ^ 2) / (Fintype.card (X → Bool) : ℝ) =
      (∑ τ : Fin (Fintype.card X) → Bool, (g τ - μ) ^ 2) / (2 ^ Fintype.card X : ℝ) := by
    rw [hcard]; congr 1; exact (Equiv.sum_comp eAll.symm (fun ω => (f ω - μ) ^ 2)).symm
  have hR : ∑ x : X,
      (∑ ω : X → Bool, (f ω - f (Function.update ω x (!ω x))) ^ 2) /
        (Fintype.card (X → Bool) : ℝ) =
      ∑ i : Fin (Fintype.card X),
        (∑ τ : Fin (Fintype.card X) → Bool, (g τ - g (Function.update τ i (!τ i))) ^ 2) /
          (2 ^ Fintype.card X : ℝ) := by
    rw [← Equiv.sum_comp eX.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcard]; congr 1
    rw [← Equiv.sum_comp eAll.symm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hupd : eAll.symm (Function.update τ i (!τ i)) =
        Function.update (eAll.symm τ) (eX.symm i) (!(eAll.symm τ (eX.symm i))) := by
      funext x
      simp only [eAll, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm]
      by_cases hx : x = eX.symm i
      · subst hx; simp
      · have hne : eX x ≠ i := fun h => hx (eX.symm_apply_eq.mpr h.symm).symm
        simp [hx, hne]
    simp only [g, hupd]
  rw [hL, hR, hμ_eq]
  exact efron_stein_fin (Fintype.card X) g

end FiniteProb


/- ### Section 3: Typical Properties of `G(n, 1/2)` (Operator Norm & Uniform Anti-Concentration) -/

section TypicalGraph

/-- Explicit integer `1/8`-net of the Euclidean unit ball in `ℝ^n` via `ℓ_1` budget `≤ 5 * n`. -/
def l1BallInt (n : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(5 * (n : ℤ))) (5 * (n : ℤ)))).filter
    (fun v => ∑ i : Fin n, (v i).natAbs ≤ 5 * n)

/-- Stars-and-bars bound: the number of `n`-tuples in `ℕ` with sum `≤ M` is at most `2^(M + n)`. -/
lemma card_nat_l1_ball (n M : ℕ) :
    ((Fintype.piFinset (fun _ : Fin n => Finset.range (M + 1))).filter
      (fun a : Fin n → ℕ => ∑ i : Fin n, a i ≤ M)).card ≤ 2 ^ (M + n) := by
  induction n generalizing M with
  | zero => simp; exact Nat.one_le_two_pow
  | succ n ih =>
    let S := (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (M + 1))).filter
      (fun a : Fin (n + 1) → ℕ => ∑ i : Fin (n + 1), a i ≤ M)
    have hpart : S.card ≤ ∑ k ∈ Finset.range (M + 1),
        ((Fintype.piFinset (fun _ : Fin n => Finset.range (M - k + 1))).filter
          (fun b : Fin n → ℕ => ∑ i : Fin n, b i ≤ M - k)).card := by
      have hcov : S ⊆ (Finset.range (M + 1)).biUnion (fun k =>
          ((Fintype.piFinset (fun _ : Fin n => Finset.range (M - k + 1))).filter
            (fun b : Fin n → ℕ => ∑ i : Fin n, b i ≤ M - k)).image (Fin.cons (α := fun _ => ℕ) k)) := by
        intro a ha
        rcases Finset.mem_filter.mp ha with ⟨_, hsum⟩
        rw [Fin.sum_univ_succ] at hsum
        refine Finset.mem_biUnion.mpr ⟨a 0, Finset.mem_range.mpr (by omega),
          Finset.mem_image.mpr ⟨fun i => a i.succ, Finset.mem_filter.mpr
            ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by
              have hi : a i.succ ≤ ∑ j : Fin n, a j.succ :=
                Finset.single_le_sum (f := fun j : Fin n => a j.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
              omega), Nat.le_sub_of_add_le' hsum⟩, by funext i; refine Fin.cases rfl (fun _ => rfl) i⟩⟩
      calc S.card
          ≤ _ := Finset.card_le_card hcov
        _ ≤ ∑ k ∈ Finset.range (M + 1),
              (((Fintype.piFinset (fun _ : Fin n => Finset.range (M - k + 1))).filter
                (fun b : Fin n → ℕ => ∑ i : Fin n, b i ≤ M - k)).image (Fin.cons (α := fun _ => ℕ) k)).card :=
            Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    have hgeom : ∑ k ∈ Finset.range (M + 1), 2 ^ (M - k + n) ≤ 2 ^ (M + (n + 1)) := by
      clear hpart S
      induction M with
      | zero => simp [pow_succ]
      | succ M ihM =>
        rw [Finset.sum_range_succ']
        have hrew : ∑ k ∈ Finset.range (M + 1), 2 ^ (M + 1 - (k + 1) + n) =
            ∑ k ∈ Finset.range (M + 1), 2 ^ (M - k + n) :=
          Finset.sum_congr rfl fun k _ => by congr 1; omega
        rw [hrew, Nat.sub_zero]
        have hpow : 2 ^ (M + (n + 1)) + 2 ^ (M + 1 + n) = 2 ^ (M + 1 + (n + 1)) := by
          have heq : M + (n + 1) = M + 1 + n := by omega
          rw [heq, show M + 1 + (n + 1) = (M + 1 + n) + 1 by omega, pow_succ]
          omega
        omega
    exact hpart.trans ((Finset.sum_le_sum fun k _ => ih (M - k)).trans hgeom)

lemma card_l1BallInt_le (n : ℕ) : (l1BallInt n).card ≤ 2 ^ (7 * n) := by
  let NatBall := (Fintype.piFinset (fun _ : Fin n => Finset.range (5 * n + 1))).filter
    (fun a : Fin n → ℕ => ∑ i : Fin n, a i ≤ 5 * n)
  let enc : (Fin n → Bool) × (Fin n → ℕ) → (Fin n → ℤ) :=
    fun p i => if p.1 i then (p.2 i : ℤ) else -(p.2 i : ℤ)
  have hsub : l1BallInt n ⊆ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ NatBall).image enc := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨_, hsum⟩
    refine Finset.mem_image.mpr ⟨(fun i => decide (0 ≤ v i), fun i => (v i).natAbs),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by
          dsimp only
          have hi : (v i).natAbs ≤ ∑ j : Fin n, (v j).natAbs :=
            Finset.single_le_sum (f := fun j : Fin n => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega), hsum⟩⟩, ?_⟩
    funext i
    simp only [enc]
    by_cases h0 : 0 ≤ v i
    · simp [h0, Int.natAbs_of_nonneg h0]
    · simp only [decide_eq_false h0, Bool.false_eq_true, ite_false]
      have hlt : v i < 0 := not_le.mp h0
      omega
  have hnat := card_nat_l1_ball n (5 * n)
  calc (l1BallInt n).card
      ≤ (((Finset.univ : Finset (Fin n → Bool)) ×ˢ NatBall).image enc).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ NatBall).card := Finset.card_image_le
    _ = 2 ^ n * NatBall.card := by rw [Finset.card_product, Finset.card_univ]; simp
    _ ≤ 2 ^ n * 2 ^ (5 * n + n) := Nat.mul_le_mul_left _ hnat
    _ = 2 ^ (7 * n) := by rw [← pow_add]; congr 1; omega

/-- Every unit vector `u` in `ℝ^n` is within `1/8` in `ℓ_2` of a scaled point in `l1BallInt n`. -/
lemma exists_net_approx {n : ℕ} (hn : 1 ≤ n) (u : Fin n → ℝ)
    (hu : ∑ i : Fin n, (u i) ^ 2 ≤ 1) :
    ∃ v ∈ l1BallInt n,
      ∑ i : Fin n, (u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 ≤ 1 / 64 ∧
      ∑ i : Fin n, ((v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let v : Fin n → ℤ := fun i => round (4 * Real.sqrt (n : ℝ) * u i)
  have hdiff : ∀ i : Fin n, |4 * Real.sqrt (n : ℝ) * u i - (v i : ℝ)| ≤ 1 / 2 := fun i => by
    have := abs_sub_round (4 * Real.sqrt (n : ℝ) * u i)
    simpa [v] using this
  have hL1_u : ∑ i : Fin n, |u i| ≤ Real.sqrt (n : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => |u i|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, sq_abs] at hcs
    have h1 : (∑ i : Fin n, |u i|) ^ 2 ≤ (n : ℝ) := hcs.trans (by nlinarith [hu, hn_pos])
    have h2 : (∑ i : Fin n, |u i|) ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by
      rwa [Real.sq_sqrt hn_pos.le]
    nlinarith [h2, Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (u i)),
      Real.sqrt_nonneg (n : ℝ)]
  have hL1_v : ∑ i : Fin n, (v i).natAbs ≤ 5 * n := by
    have hR : (∑ i : Fin n, ((v i).natAbs : ℝ)) ≤ 5 * (n : ℝ) := by
      have hterm : ∀ i : Fin n, ((v i).natAbs : ℝ) ≤ 4 * Real.sqrt (n : ℝ) * |u i| + 1 / 2 := by
        intro i
        have h1 : ((v i).natAbs : ℝ) = |(v i : ℝ)| := by simp [Int.cast_abs]
        have h2 : |(v i : ℝ)| ≤ |4 * Real.sqrt (n : ℝ) * u i| + 1 / 2 := by
          have := hdiff i
          have htri := abs_sub_abs_le_abs_sub (v i : ℝ) (4 * Real.sqrt (n : ℝ) * u i)
          rw [abs_sub_comm] at htri
          linarith
        rw [h1]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.sqrt (n : ℝ))] at h2
        exact h2
      calc ∑ i : Fin n, ((v i).natAbs : ℝ)
          ≤ ∑ i : Fin n, (4 * Real.sqrt (n : ℝ) * |u i| + 1 / 2) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = 4 * Real.sqrt (n : ℝ) * (∑ i : Fin n, |u i|) + (n : ℝ) / 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ 4 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) + (n : ℝ) / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hL1_u (by positivity)) le_rfl
        _ = 4 * (n : ℝ) + (n : ℝ) / 2 := by
            rw [mul_assoc, Real.mul_self_sqrt hn_pos.le]
        _ ≤ 5 * (n : ℝ) := by linarith
    exact_mod_cast hR
  have hv_mem : v ∈ l1BallInt n := by
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_, hL1_v⟩
    have hi : (v i).natAbs ≤ 5 * n :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hL1_v
    omega
  have herr : ∑ i : Fin n, (u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 ≤ 1 / 64 := by
    have hterm : ∀ i : Fin n, (u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 ≤ 1 / (64 * (n : ℝ)) := by
      intro i
      have h1 : |u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))| ≤ 1 / (8 * Real.sqrt (n : ℝ)) := by
        have heq : u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ)) =
            (4 * Real.sqrt (n : ℝ) * u i - (v i : ℝ)) / (4 * Real.sqrt (n : ℝ)) := by
          field_simp
        rw [heq, abs_div, abs_of_pos (by positivity : 0 < 4 * Real.sqrt (n : ℝ))]
        calc |4 * Real.sqrt (n : ℝ) * u i - (v i : ℝ)| / (4 * Real.sqrt (n : ℝ))
            ≤ (1 / 2) / (4 * Real.sqrt (n : ℝ)) :=
              div_le_div_of_nonneg_right (hdiff i) (by positivity)
          _ = 1 / (8 * Real.sqrt (n : ℝ)) := by ring
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, div_pow, one_pow, mul_pow, Real.sq_sqrt hn_pos.le] at h2
      linarith [h2, show (8 : ℝ) ^ 2 * (n : ℝ) = 64 * (n : ℝ) by ring]
    calc ∑ i : Fin n, (u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2
        ≤ ∑ _i : Fin n, (1 / (64 * (n : ℝ))) := Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * (1 / (64 * (n : ℝ))) := by simp
      _ = 1 / 64 := by field_simp
  have hnorm : ∑ i : Fin n, ((v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin n => u i) (fun i => (v i : ℝ) / (4 * Real.sqrt (n : ℝ)) - u i)
    have hcross : |∑ i : Fin n, u i * ((v i : ℝ) / (4 * Real.sqrt (n : ℝ)) - u i)| ≤ 1 / 8 := by
      have h1 : (∑ i : Fin n, u i * ((v i : ℝ) / (4 * Real.sqrt (n : ℝ)) - u i)) ^ 2 ≤ 1 / 64 := by
        have herr' : ∑ i : Fin n, ((v i : ℝ) / (4 * Real.sqrt (n : ℝ)) - u i) ^ 2 ≤ 1 / 64 := by
          convert herr using 2; ring
        exact hcs.trans (mul_le_mul hu herr' (Finset.sum_nonneg fun _ _ => sq_nonneg _) zero_le_one |> fun h => by linarith)
      rw [abs_le]
      constructor <;> nlinarith [h1]
    have hexp : ∑ i : Fin n, ((v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 =
        (∑ i : Fin n, (u i) ^ 2) +
        2 * (∑ i : Fin n, u i * ((v i : ℝ) / (4 * Real.sqrt (n : ℝ)) - u i)) +
        ∑ i : Fin n, (u i - (v i : ℝ) / (4 * Real.sqrt (n : ℝ))) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hexp]
    have hle := (abs_le.mp hcross).2
    linarith [hu, herr, hle]
  exact ⟨v, hv_mem, herr, hnorm⟩

/-- Matrix operator-norm bound: `‖A(ω) / √n‖_op ≤ 20` fails with probability at most `2 * exp(-2 n)`. -/
theorem op_norm_bad_bound {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
        20 * Real.sqrt (n : ℝ) < |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|)).card : ℝ) ≤
      2 * Real.exp (-2 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let scale : (Fin n → ℤ) → (Fin n → ℝ) := fun v i => (v i : ℝ) / (4 * Real.sqrt (n : ℝ))
  let GoodNet := (l1BallInt n).filter (fun v => ∑ i, (scale v i) ^ 2 ≤ (9 / 8 : ℝ) ^ 2)
  let BadPair : (Fin n → ℤ) × (Fin n → ℤ) → Finset (EdgeIdx n → Bool) := fun p =>
    Finset.univ.filter (fun ω =>
      10 * Real.sqrt (n : ℝ) ≤ |∑ i : Fin n, ∑ j : Fin n, scale p.1 i * adjSign ω i j * scale p.2 j|)
  -- First show that any `ω` with `opNorm > 20 √n` lies in `BadPair p` for some `p ∈ GoodNet ×ˢ GoodNet`.
  have hcov : Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
        20 * Real.sqrt (n : ℝ) < |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|) ⊆
      (GoodNet ×ˢ GoodNet).biUnion BadPair := by
    intro ω hω
    by_contra hnot
    simp only [Finset.mem_biUnion, Finset.mem_product, not_exists, not_and] at hnot
    have hnet_lt : ∀ v₁ ∈ GoodNet, ∀ v₂ ∈ GoodNet,
        |∑ i : Fin n, ∑ j : Fin n, scale v₁ i * adjSign ω i j * scale v₂ j| < 10 * Real.sqrt (n : ℝ) := by
      intro v₁ hv₁ v₂ hv₂
      have hnm := hnot (v₁, v₂) ⟨hv₁, hv₂⟩
      simp only [BadPair, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnm
      exact hnm
    -- Let `M` be the finite supremum of `|x^T A y|` on the unit ball (exists by compactness, or just
    -- bootstrap via a maximal-achieving pair from `IsCompact` on `EuclideanSpace`? Even simpler:
    -- `‖A‖_op ≤ ∑_{i,j} |A_{ij}| ≤ n^2`, so `sSup` exists in `ℝ`!).
    let B : Set ℝ := {val | ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
      val = |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|}
    have hB_ne : B.Nonempty := ⟨0, fun _ => 0, fun _ => 0, by simp, by simp, by simp⟩
    have hB_bdd : BddAbove B := by
      refine ⟨(n : ℝ) ^ 2, ?_⟩
      rintro val ⟨x, y, hx, hy, rfl⟩
      have hxi : ∀ i, |x i| ≤ 1 := fun i => by
        have h1 : (x i) ^ 2 ≤ 1 :=
          (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans hx
        rw [abs_le]; constructor <;> nlinarith
      have hyj : ∀ j, |y j| ≤ 1 := fun j => by
        have h1 : (y j) ^ 2 ≤ 1 :=
          (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans hy
        rw [abs_le]; constructor <;> nlinarith
      have hadj : ∀ i j, |adjSign ω i j| ≤ 1 := fun i j => by
        unfold adjSign; split_ifs <;> norm_num
      calc |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|
          ≤ ∑ i : Fin n, |∑ j : Fin n, x i * adjSign ω i j * y j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, |x i * adjSign ω i j * y j| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_mul]
            calc |x i| * |adjSign ω i j| * |y j| ≤ 1 * 1 * 1 :=
                  mul_le_mul (mul_le_mul (hxi i) (hadj i j) (abs_nonneg _) zero_le_one)
                    (hyj j) (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
        _ = (n : ℝ) ^ 2 := by simp [sq]
    let M : ℝ := sSup B
    have hM_ge : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
        |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ M :=
      fun x y hx hy => le_csSup hB_bdd ⟨x, y, hx, hy, rfl⟩
    have hM_bilin : ∀ (x y : Fin n → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b →
        (∑ i, (x i) ^ 2 ≤ a ^ 2) → (∑ i, (y i) ^ 2 ≤ b ^ 2) →
        |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ a * b * M := by
      intro x y a b ha hb hx hy
      by_cases ha0 : a = 0
      · subst ha0
        have hx0 : ∀ i, x i = 0 := fun i => by
          have : (x i) ^ 2 ≤ 0 :=
            (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans (by simpa using hx)
          nlinarith
        simp [hx0]
      by_cases hb0 : b = 0
      · subst hb0
        have hy0 : ∀ j, y j = 0 := fun j => by
          have : (y j) ^ 2 ≤ 0 :=
            (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans (by simpa using hy)
          nlinarith
        simp [hy0]
      have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hx' : ∑ i, (x i / a) ^ 2 ≤ 1 := by
        simp_rw [div_pow, ← Finset.sum_div]; exact (div_le_one (sq_pos_of_pos hap)).mpr hx
      have hy' : ∑ i, (y i / b) ^ 2 ≤ 1 := by
        simp_rw [div_pow, ← Finset.sum_div]; exact (div_le_one (sq_pos_of_pos hbp)).mpr hy
      have hm := hM_ge (fun i => x i / a) (fun j => y j / b) hx' hy'
      have hfac : (∑ i : Fin n, ∑ j : Fin n, (x i / a) * adjSign ω i j * (y j / b)) =
          (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j) / (a * b) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => by field_simp
      rw [hfac, abs_div, abs_of_pos (mul_pos hap hbp), div_le_iff₀ (mul_pos hap hbp)] at hm
      linarith
    have hM_le : M ≤ 10 * Real.sqrt (n : ℝ) + (1 / 2) * M := by
      refine csSup_le hB_ne ?_
      rintro val ⟨x, y, hx, hy, rfl⟩
      obtain ⟨v₁, hv₁, herr₁, hnorm₁⟩ := exists_net_approx hn x hx
      obtain ⟨v₂, hv₂, herr₂, hnorm₂⟩ := exists_net_approx hn y hy
      have hv₁G : v₁ ∈ GoodNet := Finset.mem_filter.mpr ⟨hv₁, hnorm₁⟩
      have hv₂G : v₂ ∈ GoodNet := Finset.mem_filter.mpr ⟨hv₂, hnorm₂⟩
      have hdecomp : (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j) =
          (∑ i : Fin n, ∑ j : Fin n, scale v₁ i * adjSign ω i j * scale v₂ j) +
          (∑ i : Fin n, ∑ j : Fin n, (x i - scale v₁ i) * adjSign ω i j * scale v₂ j) +
          (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * (y j - scale v₂ j)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      have ht1 := (hnet_lt v₁ hv₁G v₂ hv₂G).le
      have ht2 := hM_bilin (fun i => x i - scale v₁ i) (scale v₂) (1 / 8) (9 / 8)
        (by norm_num) (by norm_num) (by norm_num; exact herr₁) hnorm₂
      have ht3 := hM_bilin x (fun j => y j - scale v₂ j) 1 (1 / 8)
        zero_le_one (by norm_num) (by norm_num; exact hx) (by norm_num; exact herr₂)
      have hM_nn : 0 ≤ M := le_csSup hB_bdd hB_ne.some_mem |> fun _ => by
        exact (abs_nonneg _).trans (hM_ge (fun _ => 0) (fun _ => 0) (by simp) (by simp))
      rw [hdecomp]
      have htri1 := abs_add_le
        ((∑ i, ∑ j, scale v₁ i * adjSign ω i j * scale v₂ j) +
          ∑ i, ∑ j, (x i - scale v₁ i) * adjSign ω i j * scale v₂ j)
        (∑ i, ∑ j, x i * adjSign ω i j * (y j - scale v₂ j))
      have htri2 := abs_add_le
        (∑ i, ∑ j, scale v₁ i * adjSign ω i j * scale v₂ j)
        (∑ i, ∑ j, (x i - scale v₁ i) * adjSign ω i j * scale v₂ j)
      linarith [htri1, htri2, ht1, ht2, ht3, hM_nn]
    rcases (Finset.mem_filter.mp hω).2 with ⟨x, y, hx, hy, hgt⟩
    linarith [hM_ge x y hx hy, hM_le, hgt]
  -- Now apply Rademacher Hoeffding to each pair `p ∈ GoodNet ×ˢ GoodNet`.
  have hpair : ∀ p ∈ GoodNet ×ˢ GoodNet,
      ((BadPair p).card : ℝ) ≤ 2 * Real.exp (-12.5 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hn1 : ∑ i, (scale p.1 i) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := (Finset.mem_filter.mp hp1).2
    have hn2 : ∑ i, (scale p.2 i) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := (Finset.mem_filter.mp hp2).2
    let c : EdgeIdx n → ℝ := fun e => scale p.1 e.1.1 * scale p.2 e.1.2 + scale p.1 e.1.2 * scale p.2 e.1.1
    have hsum_eq : ∀ ω : EdgeIdx n → Bool,
        (∑ i : Fin n, ∑ j : Fin n, scale p.1 i * adjSign ω i j * scale p.2 j) =
        ∑ e : EdgeIdx n, if ω e then c e else -c e := by
      intro ω
      have h1 : (∑ i : Fin n, ∑ j : Fin n, scale p.1 i * adjSign ω i j * scale p.2 j) =
          (∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2),
            scale p.1 q.1 * adjSign ω q.1 q.2 * scale p.2 q.2) +
          (∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.2 < q.1),
            scale p.1 q.1 * adjSign ω q.1 q.2 * scale p.2 q.2) := by
        rw [← Finset.sum_product', Finset.univ_product_univ]
        have hpart : (Finset.univ : Finset (Fin n × Fin n)) =
            (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2)) ∪
            (Finset.univ.filter (fun q : Fin n × Fin n => q.2 < q.1)) ∪
            (Finset.univ.filter (fun q : Fin n × Fin n => q.1 = q.2)) := by
          ext ⟨i, j⟩
          simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
          rcases lt_trichotomy i j with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
        have hd1 : Disjoint (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
            (Finset.univ.filter (fun q : Fin n × Fin n => q.2 < q.1)) := by
          rw [Finset.disjoint_left]; intro q h1 h2
          exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        have hd2 : Disjoint ((Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2)) ∪
            (Finset.univ.filter (fun q : Fin n × Fin n => q.2 < q.1)))
            (Finset.univ.filter (fun q : Fin n × Fin n => q.1 = q.2)) := by
          rw [Finset.disjoint_left]; intro q h1 h2
          have heq := (Finset.mem_filter.mp h2).2
          rcases Finset.mem_union.mp h1 with hlt | hgt
          · exact ne_of_lt (Finset.mem_filter.mp hlt).2 heq
          · exact ne_of_gt (Finset.mem_filter.mp hgt).2 heq
        conv_lhs => rw [hpart]
        rw [Finset.sum_union hd2, Finset.sum_union hd1]
        have hdiag : ∑ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.1 = q.2),
            scale p.1 q.1 * adjSign ω q.1 q.2 * scale p.2 q.2 = 0 :=
          Finset.sum_eq_zero fun q hq => by
            rw [(Finset.mem_filter.mp hq).2, adjSign_diag, mul_zero, zero_mul]
        rw [hdiag, add_zero]
      have hswap : ∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.2 < q.1),
          scale p.1 q.1 * adjSign ω q.1 q.2 * scale p.2 q.2 =
          ∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2),
            scale p.1 q.2 * adjSign ω q.1 q.2 * scale p.2 q.1 := by
        refine Finset.sum_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_ ?_
        · intro q hq; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
        · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
        · intro ⟨a, b⟩ hab
          exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩, rfl⟩
        · intro q _; rw [adjSign_symm]
      rw [h1, hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_bij (fun q hq => ⟨q, (Finset.mem_filter.mp hq).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro e _; exact ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, Subtype.ext rfl⟩
      · intro q hq
        have hlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
        simp only [adjSign, dif_pos hlt, c]
        cases ω ⟨q, hlt⟩
        · simp; ring
        · simp
    have hc_sq : ∑ e : EdgeIdx n, (c e) ^ 2 ≤ 4 := by
      have h1 : ∑ e : EdgeIdx n, (c e) ^ 2 ≤
          2 * ∑ i : Fin n, ∑ j : Fin n, (scale p.1 i) ^ 2 * (scale p.2 j) ^ 2 := by
        have hlt_le : ∑ e : EdgeIdx n, (c e) ^ 2 ≤
            ∑ e : EdgeIdx n, (2 * ((scale p.1 e.1.1) ^ 2 * (scale p.2 e.1.2) ^ 2) +
              2 * ((scale p.1 e.1.2) ^ 2 * (scale p.2 e.1.1) ^ 2)) := by
          refine Finset.sum_le_sum fun e _ => ?_
          simp only [c]
          nlinarith [sq_nonneg (scale p.1 e.1.1 * scale p.2 e.1.2 - scale p.1 e.1.2 * scale p.2 e.1.1)]
        have hsplit : ∑ e : EdgeIdx n, (2 * ((scale p.1 e.1.1) ^ 2 * (scale p.2 e.1.2) ^ 2) +
              2 * ((scale p.1 e.1.2) ^ 2 * (scale p.2 e.1.1) ^ 2)) =
            2 * ((∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2),
                (scale p.1 q.1) ^ 2 * (scale p.2 q.2) ^ 2) +
              (∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.2 < q.1),
                (scale p.1 q.1) ^ 2 * (scale p.2 q.2) ^ 2)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
          congr 1
          congr 1
          · refine Finset.sum_bij (fun e _ => e.1) ?_ ?_ ?_ ?_
            · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
            · intro _ _ _ _ h; exact Subtype.ext h
            · intro q hq; exact ⟨⟨q, (Finset.mem_filter.mp hq).2⟩, Finset.mem_univ _, rfl⟩
            · intro _ _; rfl
          · refine Finset.sum_bij (fun e _ => (e.1.2, e.1.1)) ?_ ?_ ?_ ?_
            · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
            · intro e₁ _ e₂ _ h
              simp only [Prod.mk.injEq] at h
              exact Subtype.ext (Prod.ext h.2 h.1)
            · intro q hq; exact ⟨⟨(q.2, q.1), (Finset.mem_filter.mp hq).2⟩, Finset.mem_univ _, rfl⟩
            · intro _ _; rfl
        have hdisj : Disjoint (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
            (Finset.univ.filter (fun q : Fin n × Fin n => q.2 < q.1)) := by
          rw [Finset.disjoint_left]; intro q h1 h2
          exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        have hle_univ : (∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2),
              (scale p.1 q.1) ^ 2 * (scale p.2 q.2) ^ 2) +
            (∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.2 < q.1),
              (scale p.1 q.1) ^ 2 * (scale p.2 q.2) ^ 2) ≤
            ∑ i : Fin n, ∑ j : Fin n, (scale p.1 i) ^ 2 * (scale p.2 j) ^ 2 := by
          rw [← Finset.sum_union hdisj, ← Finset.sum_product']
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
        linarith [hlt_le, hsplit, hle_univ]
      have hfac : ∑ i : Fin n, ∑ j : Fin n, (scale p.1 i) ^ 2 * (scale p.2 j) ^ 2 =
          (∑ i : Fin n, (scale p.1 i) ^ 2) * (∑ j : Fin n, (scale p.2 j) ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      rw [hfac] at h1
      have hprod : (∑ i : Fin n, (scale p.1 i) ^ 2) * (∑ j : Fin n, (scale p.2 j) ^ 2) ≤
          (9 / 8 : ℝ) ^ 2 * (9 / 8 : ℝ) ^ 2 :=
        mul_le_mul hn1 hn2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      linarith [h1, hprod, show (2 : ℝ) * ((9 / 8 : ℝ) ^ 2 * (9 / 8 : ℝ) ^ 2) ≤ 4 by norm_num]
    have hhoef := rademacher_hoeffding c 4 (10 * Real.sqrt (n : ℝ)) (by norm_num) (by positivity) hc_sq
    have hfilt : BadPair p = Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
        10 * Real.sqrt (n : ℝ) ≤ |∑ e : EdgeIdx n, if ω e then c e else -c e|) := by
      ext ω; simp only [BadPair, Finset.mem_filter, Finset.mem_univ, true_and, hsum_eq ω]
    have hexp_eq : -(10 * Real.sqrt (n : ℝ)) ^ 2 / (2 * 4) = -12.5 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hn_pos.le]; ring
    rw [hexp_eq] at hhoef
    rw [hfilt]
    exact hhoef
  have hGood_card : ((GoodNet ×ˢ GoodNet).card : ℝ) ≤ (2 ^ (14 * n) : ℝ) := by
    have h1 : GoodNet.card ≤ 2 ^ (7 * n) :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_l1BallInt_le n)
    have h2 : (GoodNet ×ˢ GoodNet).card ≤ 2 ^ (14 * n) := by
      rw [Finset.card_product]
      calc GoodNet.card * GoodNet.card ≤ 2 ^ (7 * n) * 2 ^ (7 * n) := Nat.mul_le_mul h1 h1
        _ = 2 ^ (14 * n) := by rw [← pow_add]; congr 1; omega
    exact_mod_cast h2
  have hlog2 : (2 : ℝ) ^ (14 * n) * Real.exp (-12.5 * (n : ℝ)) ≤ Real.exp (-2 * (n : ℝ)) := by
    have h2e : (2 : ℝ) ≤ Real.exp (3 / 4) := by
      have h1 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 4
      simp [Finset.sum_range_succ, Nat.factorial] at h1
      linarith
    have hpow : (2 : ℝ) ^ (14 * n) ≤ Real.exp (10.5 * (n : ℝ)) := by
      calc (2 : ℝ) ^ (14 * n) ≤ (Real.exp (3 / 4)) ^ (14 * n) :=
            pow_le_pow_left₀ zero_le_two h2e (14 * n)
        _ = Real.exp (((14 * n : ℕ) : ℝ) * (3 / 4)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (10.5 * (n : ℝ)) := by push_cast; congr 1; ring
    calc (2 : ℝ) ^ (14 * n) * Real.exp (-12.5 * (n : ℝ))
        ≤ Real.exp (10.5 * (n : ℝ)) * Real.exp (-12.5 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = Real.exp (-2 * (n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  have hsum_bd : (((GoodNet ×ˢ GoodNet).biUnion BadPair).card : ℝ) ≤
      2 * Real.exp (-2 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
    have h1 : (((GoodNet ×ˢ GoodNet).biUnion BadPair).card : ℝ) ≤
        ∑ p ∈ GoodNet ×ˢ GoodNet, ((BadPair p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    calc (((GoodNet ×ˢ GoodNet).biUnion BadPair).card : ℝ)
        ≤ ∑ p ∈ GoodNet ×ˢ GoodNet, ((BadPair p).card : ℝ) := h1
      _ ≤ ∑ _p ∈ GoodNet ×ˢ GoodNet,
            (2 * Real.exp (-12.5 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ)) :=
          Finset.sum_le_sum hpair
      _ = ((GoodNet ×ˢ GoodNet).card : ℝ) *
            (2 * Real.exp (-12.5 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ (14 * n) : ℝ) *
            (2 * Real.exp (-12.5 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ)) :=
          mul_le_mul_of_nonneg_right hGood_card (by positivity)
      _ = 2 * ((2 : ℝ) ^ (14 * n) * Real.exp (-12.5 * (n : ℝ))) *
            (Fintype.card (EdgeIdx n → Bool) : ℝ) := by ring
      _ ≤ 2 * Real.exp (-2 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2 zero_le_two)
            (Nat.cast_nonneg _)
  exact (Nat.cast_le.mpr (Finset.card_le_card hcov)).trans hsum_bd

/-- Anti-concentration for a balanced Rademacher sum hitting a real interval of half-width `W`. -/
lemma rademacher_interval_card_le (m : ℕ) (a W : ℝ) (hW : 0 ≤ W) (σ : Fin m → Bool) :
    ((Finset.univ.filter (fun τ : Fin m → Bool =>
      |a + ∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1| ≤ W)).card : ℝ) ≤
      (W + 1) * (2 / Real.sqrt ((m : ℝ) + 1)) * (2 ^ m : ℝ) := by
  let cnt : (Fin m → Bool) → ℕ := fun τ => (Finset.univ.filter (fun j : Fin m => τ j = σ j)).card
  have hsum_cnt : ∀ τ : Fin m → Bool,
      (∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1) = 2 * (cnt τ : ℝ) - (m : ℝ) := by
    intro τ
    have hsplit : (∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1) =
        (∑ j : Fin m, if τ j = σ j then (2 : ℝ) else 0) - ∑ _j : Fin m, (1 : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [hsplit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have h2 : (∑ j : Fin m, if τ j = σ j then (2 : ℝ) else 0) = 2 * (cnt τ : ℝ) := by
      simp only [cnt, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [h2]
  let Kset : Finset ℕ := (Finset.range (m + 1)).filter
    (fun k => |a + (2 * (k : ℝ) - (m : ℝ))| ≤ W)
  have hKset_card : (Kset.card : ℝ) ≤ W + 1 := by
    by_cases hne : Kset.Nonempty
    · let kmin := Kset.min' hne
      have hkmin_mem : kmin ∈ Kset := Finset.min'_mem Kset hne
      have hkmin_bd : |a + (2 * (kmin : ℝ) - (m : ℝ))| ≤ W := (Finset.mem_filter.mp hkmin_mem).2
      have hsub : Kset ⊆ Finset.Icc kmin (kmin + Nat.floor W) := by
        intro k hk
        have hge : kmin ≤ k := Finset.min'_le Kset k hk
        have hkbd : |a + (2 * (k : ℝ) - (m : ℝ))| ≤ W := (Finset.mem_filter.mp hk).2
        have hdiff : (k : ℝ) - (kmin : ℝ) ≤ W := by
          have h1 := abs_le.mp hkmin_bd
          have h2 := abs_le.mp hkbd
          linarith
        have hnat_diff : k - kmin ≤ Nat.floor W := by
          apply Nat.le_floor
          rw [Nat.cast_sub hge]
          exact hdiff
        exact Finset.mem_Icc.mpr ⟨hge, by omega⟩
      have h1 : Kset.card ≤ Nat.floor W + 1 := by
        have h2 := Finset.card_le_card hsub
        rw [Nat.card_Icc] at h2
        omega
      have h1' : (Kset.card : ℝ) ≤ (Nat.floor W : ℝ) + 1 := by exact_mod_cast h1
      linarith [h1', Nat.floor_le hW]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      linarith
  have hfiber : ∀ k ∈ Finset.range (m + 1),
      (Finset.univ.filter (fun τ : Fin m → Bool => cnt τ = k)).card = m.choose k := by
    intro k _
    have hbij : (Finset.univ.filter (fun τ : Fin m → Bool => cnt τ = k)).card =
        ((Finset.univ : Finset (Fin m)).powersetCard k).card := by
      refine Finset.card_bij (fun τ _ => Finset.univ.filter (fun j : Fin m => τ j = σ j)) ?_ ?_ ?_
      · intro τ hτ
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hτ).2⟩
      · intro τ₁ _ τ₂ _ hEq
        funext j
        have hmem : (j ∈ Finset.univ.filter (fun j : Fin m => τ₁ j = σ j)) ↔
            (j ∈ Finset.univ.filter (fun j : Fin m => τ₂ j = σ j)) := by rw [hEq]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        cases h1 : τ₁ j <;> cases h2 : τ₂ j <;> cases h3 : σ j <;> simp_all
      · intro A hA
        rcases Finset.mem_powersetCard.mp hA with ⟨_, hcard⟩
        let τ : Fin m → Bool := fun j => if j ∈ A then σ j else !σ j
        have hfilt : Finset.univ.filter (fun j : Fin m => τ j = σ j) = A := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, τ]
          by_cases hj : j ∈ A
          · simp [hj]
          · simp [hj]
        refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hfilt⟩
        simp only [cnt, hfilt, hcard]
    rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcov : Finset.univ.filter (fun τ : Fin m → Bool =>
      |a + ∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1| ≤ W) ⊆
      Kset.biUnion (fun k => Finset.univ.filter (fun τ : Fin m → Bool => cnt τ = k)) := by
    intro τ hτ
    have hbd := (Finset.mem_filter.mp hτ).2
    rw [hsum_cnt τ] at hbd
    have hk_lt : cnt τ < m + 1 := by
      have hle : cnt τ ≤ m := by
        simpa [cnt] using Finset.card_le_univ (Finset.univ.filter (fun j : Fin m => τ j = σ j))
      omega
    exact Finset.mem_biUnion.mpr ⟨cnt τ, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, hbd⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hcard_le : ((Finset.univ.filter (fun τ : Fin m → Bool =>
      |a + ∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1| ≤ W)).card : ℝ) ≤
      ∑ k ∈ Kset, ((m.choose k : ℝ)) := by
    have hnat : (Finset.univ.filter (fun τ : Fin m → Bool =>
        |a + ∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1| ≤ W)).card ≤
        ∑ k ∈ Kset, m.choose k := by
      calc _ ≤ (Kset.biUnion (fun k => Finset.univ.filter (fun τ : Fin m → Bool => cnt τ = k))).card :=
            Finset.card_le_card hcov
        _ ≤ ∑ k ∈ Kset, (Finset.univ.filter (fun τ : Fin m → Bool => cnt τ = k)).card :=
            Finset.card_biUnion_le
        _ = ∑ k ∈ Kset, m.choose k :=
            Finset.sum_congr rfl fun k hk => hfiber k (Finset.mem_filter.mp hk).1
    exact_mod_cast hnat
  calc ((Finset.univ.filter (fun τ : Fin m → Bool =>
          |a + ∑ j : Fin m, if τ j = σ j then (1 : ℝ) else -1| ≤ W)).card : ℝ)
      ≤ ∑ k ∈ Kset, (m.choose k : ℝ) := hcard_le
    _ ≤ ∑ _k ∈ Kset, ((2 / Real.sqrt ((m : ℝ) + 1)) * (2 ^ m : ℝ)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hch := choose_div_two_pow_le m k
        have h2p : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
        exact (div_le_iff₀ h2p).mp hch
    _ = (Kset.card : ℝ) * ((2 / Real.sqrt ((m : ℝ) + 1)) * (2 ^ m : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (W + 1) * ((2 / Real.sqrt ((m : ℝ) + 1)) * (2 ^ m : ℝ)) :=
        mul_le_mul_of_nonneg_right hKset_card (by positivity)
    _ = (W + 1) * (2 / Real.sqrt ((m : ℝ) + 1)) * (2 ^ m : ℝ) := by ring

/-- Fixed-bisection, fixed-subset anti-concentration by conditioning on all edges not crossing `S`. -/
lemma fixed_subset_anticonc {n : ℕ} (s S : Finset (Fin n)) (c_anti : ℝ) (hc : 0 ≤ c_anti) :
    ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∀ v ∈ S, |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
        c_anti * Real.sqrt (n : ℝ))).card : ℝ) ≤
      ((2 * c_anti * Real.sqrt (n : ℝ) + 1) *
        (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) ^ S.card *
        (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
  let T : Finset (Fin n) := Finset.univ \ S
  have hT_card : T.card = n - S.card := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    change T.card + S.card = n at h1
    omega
  let Cross : Finset (EdgeIdx n) := Finset.univ.filter (fun e =>
    (e.1.1 ∈ S ∧ e.1.2 ∉ S) ∨ (e.1.2 ∈ S ∧ e.1.1 ∉ S))
  -- Bijection between `Cross` and `↥S × ↥T`.
  let mkEdge : ↥S × ↥T → EdgeIdx n := fun p =>
    if h : p.1.1 < p.2.1 then ⟨(p.1.1, p.2.1), h⟩
    else ⟨(p.2.1, p.1.1), lt_of_le_of_ne (not_lt.mp h) (fun hEq => by
      dsimp only at hEq
      exact (Finset.mem_sdiff.mp p.2.2).2 (hEq ▸ p.1.2))⟩
  have hmk_mem : ∀ p : ↥S × ↥T, mkEdge p ∈ Cross := by
    intro p
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hT2 : p.2.1 ∉ S := (Finset.mem_sdiff.mp p.2.2).2
    by_cases h : p.1.1 < p.2.1
    · simp only [mkEdge, dif_pos h]; exact Or.inl ⟨p.1.2, hT2⟩
    · simp only [mkEdge, dif_neg h]; exact Or.inr ⟨p.1.2, hT2⟩
  let eCross : {e : EdgeIdx n // e ∈ Cross} ≃ (↥S × ↥T) :=
    { toFun := fun e =>
        if h : e.1.1.1 ∈ S then
          ⟨⟨e.1.1.1, h⟩, ⟨e.1.1.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
            rcases (Finset.mem_filter.mp e.2).2 with ⟨_, h2⟩ | ⟨h2, h1⟩
            · exact h2
            · exact absurd h h1⟩⟩⟩
        else
          ⟨⟨e.1.1.2, by
            rcases (Finset.mem_filter.mp e.2).2 with ⟨h1, _⟩ | ⟨h2, _⟩
            · exact absurd h1 h
            · exact h2⟩,
           ⟨e.1.1.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩⟩
      invFun := fun p => ⟨mkEdge p, hmk_mem p⟩
      left_inv := fun e => by
        apply Subtype.ext
        by_cases h1 : e.1.1.1 ∈ S
        · have h2 : e.1.1.2 ∉ S := by
            rcases (Finset.mem_filter.mp e.2).2 with ⟨_, h2⟩ | ⟨_, h1'⟩
            · exact h2
            · exact absurd h1 h1'
          simp only [dif_pos h1, mkEdge, dif_pos e.1.2]
        · have h2 : e.1.1.2 ∈ S := by
            rcases (Finset.mem_filter.mp e.2).2 with ⟨h1', _⟩ | ⟨h2, _⟩
            · exact absurd h1' h1
            · exact h2
          have hnot : ¬ e.1.1.2 < e.1.1.1 := lt_asymm e.1.2
          simp only [dif_neg h1, mkEdge, dif_neg hnot]
      right_inv := fun p => by
        have hT2 : p.2.1 ∉ S := (Finset.mem_sdiff.mp p.2.2).2
        by_cases h : p.1.1 < p.2.1
        · simp only [mkEdge, dif_pos h, dif_pos p.1.2]
        · simp only [mkEdge, dif_neg h, dif_neg hT2] }
  let eSplit : (EdgeIdx n → Bool) ≃ (↥S → ↥T → Bool) × ({e : EdgeIdx n // e ∉ Cross} → Bool) :=
    { toFun := fun ω =>
        (fun u w => ω (mkEdge (u, w)), fun e => ω e.1)
      invFun := fun p e =>
        if h : e ∈ Cross then p.1 (eCross ⟨e, h⟩).1 (eCross ⟨e, h⟩).2 else p.2 ⟨e, h⟩
      left_inv := fun ω => by
        funext e
        by_cases h : e ∈ Cross
        · simp only [dif_pos h]
          have hinv := eCross.left_inv ⟨e, h⟩
          exact congrArg ω (congrArg Subtype.val hinv)
        · simp only [dif_neg h]
      right_inv := fun ⟨f, g⟩ => by
        ext u w
        · simp only [dif_pos (hmk_mem (u, w))]
          change f (eCross (eCross.symm (u, w))).1 (eCross (eCross.symm (u, w))).2 = f u w
          rw [eCross.apply_symm_apply]
        · simp only [dif_neg u.2] }
  -- Express `2 * friendliness` for `v ∈ S` as `rest(v, g) + cross(v, f v)`.
  let σ : Fin n → ℝ := fun u => if u ∈ s then (1 : ℝ) else -1
  have hval : ∀ (f : ↥S → ↥T → Bool) (g : {e : EdgeIdx n // e ∉ Cross} → Bool) (v : ↥S),
      let ω := eSplit.symm (f, g)
      (2 : ℝ) * (Green91.friendliness ((graphEquiv n).symm ω) s v.1 : ℝ) =
        (σ v.1 * (∑ w ∈ S, adjSign ω v.1 w * σ w) + σ v.1 * (∑ w : Fin n, σ w) - 1) +
        ∑ w : ↥T, if f v w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1 := by
    intro f g v ω
    rw [friendliness_eq_adjSign ω s v.1]
    have hsplit_sum : (∑ w : Fin n, adjSign ω v.1 w * σ w) =
        (∑ w ∈ S, adjSign ω v.1 w * σ w) + ∑ w ∈ T, adjSign ω v.1 w * σ w := by
      have hun : S ∪ T = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ S)
      have hd : Disjoint S T := Finset.disjoint_sdiff
      rw [← hun, Finset.sum_union hd]
    rw [hsplit_sum, mul_add, ← Finset.sum_coe_sort T (fun w => adjSign ω v.1 w * σ w)]
    have hcross_term : ∀ w : ↥T,
        σ v.1 * (adjSign ω v.1 w.1 * σ w.1) =
          if f v w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1 := by
      intro w
      have hvw_ne : v.1 ≠ w.1 := fun h => (Finset.mem_sdiff.mp w.2).2 (h ▸ v.2)
      have hω_mk : ω (mkEdge (v, w)) = f v w := by
        have hr := congrArg Prod.fst (eSplit.right_inv (f, g))
        exact congrFun (congrFun hr v) w
      have hadj : adjSign ω v.1 w.1 = if f v w then (1 : ℝ) else -1 := by
        unfold adjSign
        rcases lt_or_gt_of_ne hvw_ne with hlt | hgt
        · simp only [dif_pos hlt]
          have heq : (⟨(v.1, w.1), hlt⟩ : EdgeIdx n) = mkEdge (v, w) := by simp [mkEdge, hlt]
          rw [heq, hω_mk]
        · have hnot : ¬ v.1 < w.1 := lt_asymm hgt
          simp only [dif_neg hnot, dif_pos hgt]
          have heq : (⟨(w.1, v.1), hgt⟩ : EdgeIdx n) = mkEdge (v, w) := by simp [mkEdge, hnot]
          rw [heq, hω_mk]
      rw [hadj]
      by_cases hv : v.1 ∈ s <;> by_cases hw : w.1 ∈ s <;> cases hf : f v w <;>
        simp [σ, hv, hw]
    have hsum_eq : σ v.1 * (∑ w : ↥T, adjSign ω v.1 w.1 * σ w.1) =
        ∑ w : ↥T, if f v w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => hcross_term w
    change σ v.1 * (∑ w ∈ S, adjSign ω v.1 w * σ w) +
        σ v.1 * (∑ w : ↥T, adjSign ω v.1 w.1 * σ w.1) +
        σ v.1 * (∑ w : Fin n, σ w) - 1 = _
    rw [hsum_eq]; ring
  -- Note the `S`-internal term depends only on `g` (not on `f`).
  let aRest : ({e : EdgeIdx n // e ∉ Cross} → Bool) → ↥S → ℝ := fun g v =>
    let ω0 := eSplit.symm (fun _ _ => false, g)
    σ v.1 * (∑ w ∈ S, adjSign ω0 v.1 w * σ w) + σ v.1 * (∑ w : Fin n, σ w) - 1
  have haRest_eq : ∀ f g (v : ↥S),
      let ω := eSplit.symm (f, g)
      σ v.1 * (∑ w ∈ S, adjSign ω v.1 w * σ w) + σ v.1 * (∑ w : Fin n, σ w) - 1 = aRest g v := by
    intro f g v ω
    simp only [aRest]
    congr 3
    refine Finset.sum_congr rfl fun w hw => ?_
    congr 1
    rcases lt_trichotomy v.1 w with h1 | rfl | h2
    · have hnotC : (⟨(v.1, w), h1⟩ : EdgeIdx n) ∉ Cross := by
        simp only [Cross, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and, not_not]
        exact ⟨fun _ => hw, fun _ => v.2⟩
      simp only [adjSign, dif_pos h1, ω, eSplit, Equiv.coe_fn_symm_mk, dif_neg hnotC]
    · simp [adjSign]
    · have hnot : ¬ v.1 < w := lt_asymm h2
      have hnotC : (⟨(w, v.1), h2⟩ : EdgeIdx n) ∉ Cross := by
        simp only [Cross, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and, not_not]
        exact ⟨fun _ => v.2, fun _ => hw⟩
      simp only [adjSign, dif_neg hnot, dif_pos h2, ω, eSplit, Equiv.coe_fn_symm_mk, dif_neg hnotC]
  -- For each fixed `g`, count the valid `f : ↥S → ↥T → Bool` as a product over `v : ↥S`.
  let W : ℝ := 2 * c_anti * Real.sqrt (n : ℝ)
  have hW : 0 ≤ W := by positivity
  let SliceG : ({e : EdgeIdx n // e ∉ Cross} → Bool) → Finset (↥S → ↥T → Bool) := fun g =>
    Fintype.piFinset fun v : ↥S => Finset.univ.filter (fun row : ↥T → Bool =>
      |aRest g v + ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1| ≤ W)
  have hSlice_card : ∀ g, ((SliceG g).card : ℝ) ≤
      ((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) ^ S.card *
        (Fintype.card (↥S → ↥T → Bool) : ℝ) := by
    intro g
    have hprod : ((SliceG g).card : ℝ) =
        ∏ v : ↥S, (((Finset.univ.filter (fun row : ↥T → Bool =>
          |aRest g v + ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1| ≤ W)).card : ℝ)) := by
      simp only [SliceG, Fintype.card_piFinset, Nat.cast_prod]
    rw [hprod]
    let eT : ↥T ≃ Fin (n - S.card) := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hT_card])
    let eRow : (↥T → Bool) ≃ (Fin (n - S.card) → Bool) := Equiv.arrowCongr eT (Equiv.refl Bool)
    have hfactor : ∀ v : ↥S,
        ((Finset.univ.filter (fun row : ↥T → Bool =>
          |aRest g v + ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1| ≤ W)).card : ℝ) ≤
        ((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) * (2 ^ (n - S.card) : ℝ) := by
      intro v
      have hcard_eq : (Finset.univ.filter (fun row : ↥T → Bool =>
          |aRest g v + ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1| ≤ W)).card =
          (Finset.univ.filter (fun τ : Fin (n - S.card) → Bool =>
            |aRest g v + ∑ j : Fin (n - S.card),
              if τ j = decide (v.1 ∈ s ↔ (eT.symm j).1 ∈ s) then (1 : ℝ) else -1| ≤ W)).card := by
        refine Finset.card_bij (fun row _ => eRow row) ?_ ?_ ?_
        · intro row hrow
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
          have hse : ∑ j : Fin (n - S.card),
              (if eRow row j = decide (v.1 ∈ s ↔ (eT.symm j).1 ∈ s) then (1 : ℝ) else -1) =
              ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1 := by
            rw [← Equiv.sum_comp eT.symm]
            refine Finset.sum_congr rfl fun j _ => by simp [eRow]
          rwa [hse]
        · intro _ _ _ _ h; exact eRow.injective h
        · intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          refine ⟨eRow.symm τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eRow.apply_symm_apply τ⟩
          have hse : ∑ w : ↥T, (if eRow.symm τ w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1) =
              ∑ j : Fin (n - S.card),
                if τ j = decide (v.1 ∈ s ↔ (eT.symm j).1 ∈ s) then (1 : ℝ) else -1 := by
            rw [← Equiv.sum_comp eT.symm]
            refine Finset.sum_congr rfl fun j _ => by simp [eRow]
          rwa [hse]
      rw [hcard_eq]
      exact rademacher_interval_card_le (n - S.card) (aRest g v) W hW
        (fun j => decide (v.1 ∈ s ↔ (eT.symm j).1 ∈ s))
    have hcard_ST : (Fintype.card (↥S → ↥T → Bool) : ℝ) = ((2 ^ (n - S.card) : ℝ)) ^ S.card := by
      have h1 : Fintype.card (↥S → ↥T → Bool) = (2 ^ (n - S.card)) ^ S.card := by
        simp [hT_card]
      exact_mod_cast h1
    calc ∏ v : ↥S, ((Finset.univ.filter (fun row : ↥T → Bool =>
            |aRest g v + ∑ w : ↥T, if row w = decide (v.1 ∈ s ↔ w.1 ∈ s) then (1 : ℝ) else -1| ≤ W)).card : ℝ)
        ≤ ∏ _v : ↥S, (((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) * (2 ^ (n - S.card) : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun v _ => hfactor v
      _ = (((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) * (2 ^ (n - S.card) : ℝ)) ^ S.card := by
          simp [Finset.prod_const]
      _ = ((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) ^ S.card *
            (Fintype.card (↥S → ↥T → Bool) : ℝ) := by
          rw [mul_pow, hcard_ST]
  -- Sum over `g` via `eSplit`.
  have hsum_ev : ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∀ v ∈ S, |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
        c_anti * Real.sqrt (n : ℝ))).card : ℝ) =
      ∑ g : {e : EdgeIdx n // e ∉ Cross} → Bool, ((SliceG g).card : ℝ) := by
    have h1 : ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
        ∀ v ∈ S, |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
          c_anti * Real.sqrt (n : ℝ))).card : ℝ) =
        ∑ ω : EdgeIdx n → Bool,
          if ∀ v ∈ S, |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
            c_anti * Real.sqrt (n : ℝ) then (1 : ℝ) else 0 := by
      rw [Finset.card_filter]; simp
    rw [h1, ← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have h2 : ((SliceG g).card : ℝ) =
        ∑ f : ↥S → ↥T → Bool, if f ∈ SliceG g then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [h2]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hiff : (∀ v ∈ S, |(Green91.friendliness ((graphEquiv n).symm (eSplit.symm (f, g))) s v : ℝ)| ≤
        c_anti * Real.sqrt (n : ℝ)) ↔ f ∈ SliceG g := by
      simp only [SliceG, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hall v
        have hv := hall v.1 v.2
        have hv2 : |(2 : ℝ) * (Green91.friendliness ((graphEquiv n).symm (eSplit.symm (f, g))) s v.1 : ℝ)| ≤ W := by
          rw [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
          simp only [W]; linarith
        rwa [hval f g v, haRest_eq f g v] at hv2
      · intro hall v hv
        have hfv := hall ⟨v, hv⟩
        rw [← haRest_eq f g ⟨v, hv⟩, ← hval f g ⟨v, hv⟩, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hfv
        simp only [W] at hfv
        linarith
    exact if_congr hiff rfl rfl
  have htot : (Fintype.card (EdgeIdx n → Bool) : ℝ) =
      (Fintype.card (↥S → ↥T → Bool) : ℝ) *
      (Fintype.card ({e : EdgeIdx n // e ∉ Cross} → Bool) : ℝ) := by
    have h1 : Fintype.card (EdgeIdx n → Bool) =
        Fintype.card (↥S → ↥T → Bool) * Fintype.card ({e : EdgeIdx n // e ∉ Cross} → Bool) := by
      rw [Fintype.card_congr eSplit, Fintype.card_prod]
    exact_mod_cast h1
  rw [hsum_ev, htot]
  calc ∑ g : {e : EdgeIdx n // e ∉ Cross} → Bool, ((SliceG g).card : ℝ)
      ≤ ∑ _g : {e : EdgeIdx n // e ∉ Cross} → Bool,
          (((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) ^ S.card *
            (Fintype.card (↥S → ↥T → Bool) : ℝ)) :=
        Finset.sum_le_sum fun g _ => hSlice_card g
    _ = ((W + 1) * (2 / Real.sqrt (((n - S.card : ℕ) : ℝ) + 1))) ^ S.card *
          ((Fintype.card (↥S → ↥T → Bool) : ℝ) *
          (Fintype.card ({e : EdgeIdx n // e ∉ Cross} → Bool) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Uniform anti-concentration across all `2^n` bisections: w.h.p. no bisection has `≥ δ n`
vertices with `|friendliness| ≤ c_anti * √n`. -/
theorem all_bisections_anticonc {n : ℕ} {δ c_anti : ℝ}
    (hδ0 : 0 < δ) (hδ_half : δ ≤ 1 / 4) (hc0 : 0 < c_anti)
    (hc_small : 6 * c_anti + 4 / Real.sqrt (n : ℝ) ≤ (1 / 8 : ℝ) ^ (Nat.ceil (1 / δ)))
    (hn : 16 ≤ n) :
    ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∃ s : Finset (Fin n),
        δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
            c_anti * Real.sqrt (n : ℝ))).card : ℝ))).card : ℝ) ≤
      (1 / 2 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let kS : ℕ := Nat.ceil (δ * (n : ℝ))
  have hkS_ge : δ * (n : ℝ) ≤ (kS : ℝ) := Nat.le_ceil _
  have hkS_le : kS ≤ n / 2 := by
    have h1 : δ * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      have h2 : (n : ℝ) / 4 ≤ ((n / 2 : ℕ) : ℝ) := by
        have hnat : n ≤ 4 * (n / 2) := by omega
        have hR : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
        linarith
      nlinarith [hδ_half, hn_pos, h2]
    exact Nat.ceil_le.mpr h1
  let M : ℕ := Nat.ceil (1 / δ)
  have hM_ge : 1 / δ ≤ (M : ℝ) := Nat.le_ceil _
  have hn_le_Mk : n ≤ M * kS := by
    have hR : (n : ℝ) ≤ (M : ℝ) * (kS : ℝ) := by
      have h1 : (1 / δ) * (δ * (n : ℝ)) = (n : ℝ) := by field_simp
      calc (n : ℝ) = (1 / δ) * (δ * (n : ℝ)) := h1.symm
        _ ≤ (M : ℝ) * (kS : ℝ) := mul_le_mul hM_ge hkS_ge (by positivity) (by positivity)
    exact_mod_cast hR
  let SubK : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => S.card = kS)
  let BadSS : Finset (Fin n) × Finset (Fin n) → Finset (EdgeIdx n → Bool) := fun p =>
    Finset.univ.filter (fun ω => ∀ v ∈ p.2,
      |(Green91.friendliness ((graphEquiv n).symm ω) p.1 v : ℝ)| ≤ c_anti * Real.sqrt (n : ℝ))
  have hcov : Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
      ∃ s : Finset (Fin n),
        δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
            c_anti * Real.sqrt (n : ℝ))).card : ℝ)) ⊆
      ((Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK).biUnion BadSS := by
    intro ω hω
    rcases (Finset.mem_filter.mp hω).2 with ⟨s, hs⟩
    have hcard_ge : kS ≤ (Finset.univ.filter (fun v : Fin n =>
        |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
          c_anti * Real.sqrt (n : ℝ))).card := Nat.ceil_le.mpr hs
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard_ge
    refine Finset.mem_biUnion.mpr ⟨(s, S),
      Finset.mem_product.mpr ⟨Finset.mem_univ s, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hScard⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ ω, fun v hv => (Finset.mem_filter.mp (hSsub hv)).2⟩⟩
  have hbase_le : (2 * c_anti * Real.sqrt (n : ℝ) + 1) *
      (2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1)) ≤ (1 / 8 : ℝ) ^ M := by
    have hsub_ge : (n : ℝ) / 2 ≤ ((n - kS : ℕ) : ℝ) + 1 := by
      have h1 : n ≤ 2 * (n - kS + 1) := by omega
      have h1' : (n : ℝ) ≤ 2 * (((n - kS : ℕ) : ℝ) + 1) := by exact_mod_cast h1
      linarith
    have hsqrt_ge : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt (((n - kS : ℕ) : ℝ) + 1) := by
      have hsq : (Real.sqrt (n : ℝ) / 2) ^ 2 ≤ (Real.sqrt (((n - kS : ℕ) : ℝ) + 1)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hn_pos.le, Real.sq_sqrt (by positivity)]
        linarith [hsub_ge]
      nlinarith [hsq, Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (((n - kS : ℕ) : ℝ) + 1)]
    have hdiv_le : 2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1) ≤ 4 / Real.sqrt (n : ℝ) := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hsq_pos]
      linarith [hsqrt_ge]
    have hprod : (2 * c_anti * Real.sqrt (n : ℝ) + 1) *
        (2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1)) ≤
        (2 * c_anti * Real.sqrt (n : ℝ) + 1) * (4 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv_le (by positivity)
    have hsimp : (2 * c_anti * Real.sqrt (n : ℝ) + 1) * (4 / Real.sqrt (n : ℝ)) =
        8 * c_anti + 4 / Real.sqrt (n : ℝ) := by field_simp; ring
    -- Wait: `8 * c_anti` vs `6 * c_anti`! Tighten `hsqrt_ge` to `Real.sqrt (n / 2)` (`2 / √(n/2) = 2 √2 / √n ≤ 3 / √n`)!
    have hsqrt_ge2 : Real.sqrt (n : ℝ) * (2 / 3) ≤ Real.sqrt (((n - kS : ℕ) : ℝ) + 1) := by
      have hsq : (Real.sqrt (n : ℝ) * (2 / 3)) ^ 2 ≤ (Real.sqrt (((n - kS : ℕ) : ℝ) + 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn_pos.le, Real.sq_sqrt (by positivity)]
        linarith [hsub_ge]
      nlinarith [hsq, Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (((n - kS : ℕ) : ℝ) + 1)]
    have hdiv_le2 : 2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1) ≤ 3 / Real.sqrt (n : ℝ) := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hsq_pos]
      linarith [hsqrt_ge2]
    have hprod2 : (2 * c_anti * Real.sqrt (n : ℝ) + 1) *
        (2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1)) ≤
        (2 * c_anti * Real.sqrt (n : ℝ) + 1) * (3 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv_le2 (by positivity)
    have hsimp2 : (2 * c_anti * Real.sqrt (n : ℝ) + 1) * (3 / Real.sqrt (n : ℝ)) =
        6 * c_anti + 3 / Real.sqrt (n : ℝ) := by field_simp; ring
    have h34 : 3 / Real.sqrt (n : ℝ) ≤ 4 / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hsq_pos.le
    linarith [hprod2, hsimp2, h34, hc_small]
  have hpow_le : ((2 * c_anti * Real.sqrt (n : ℝ) + 1) *
      (2 / Real.sqrt (((n - kS : ℕ) : ℝ) + 1))) ^ kS ≤ (1 / 8 : ℝ) ^ n := by
    calc _ ≤ ((1 / 8 : ℝ) ^ M) ^ kS := pow_le_pow_left₀ (by positivity) hbase_le kS
      _ = (1 / 8 : ℝ) ^ (M * kS) := (pow_mul _ M kS).symm
      _ ≤ (1 / 8 : ℝ) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn_le_Mk
  have hpair : ∀ p ∈ (Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK,
      ((BadSS p).card : ℝ) ≤ (1 / 8 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
    intro p hp
    have hSc : p.2.card = kS := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    have hbd := fixed_subset_anticonc p.1 p.2 c_anti hc0.le
    rw [hSc] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _))
  have htot_card : ((((Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK).card) : ℝ) ≤ (4 : ℝ) ^ n := by
    have h1 : ((Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK).card ≤ 2 ^ n * 2 ^ n := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
      exact Nat.mul_le_mul_left _ (by
        have := Finset.card_le_univ SubK
        simpa [Fintype.card_finset, Fintype.card_fin] using this)
    have h2 : 2 ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
    rw [h2] at h1
    exact_mod_cast h1
  have h48 : (4 : ℝ) ^ n * (1 / 8 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]; norm_num
  calc ((Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
          ∃ s : Finset (Fin n),
            δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
              |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
                c_anti * Real.sqrt (n : ℝ))).card : ℝ))).card : ℝ)
      ≤ ((((Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK).biUnion BadSS).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hcov)
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK, ((BadSS p).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK,
          ((1 / 8 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ)) :=
        Finset.sum_le_sum hpair
    _ = ((((Finset.univ : Finset (Finset (Fin n))) ×ˢ SubK).card) : ℝ) *
          ((1 / 8 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ)) :=
        mul_le_mul_of_nonneg_right htot_card (by positivity)
    _ = (1 / 2 : ℝ) ^ n * (Fintype.card (EdgeIdx n → Bool) : ℝ) := by
        rw [← mul_assoc, h48]

end TypicalGraph


/- ### Section 4: Smooth `C^2` Proximal Map, Barrier, Cutoff, and Ascent Inequality -/

section SmoothProx

/-- One-variable quadratic Taylor bound from a Lipschitz derivative via the Mean Value Theorem. -/
lemma taylor_of_deriv_lip {f f' : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hlip : ∀ x y, |f' x - f' y| ≤ M * |x - y|) (a h : ℝ) :
    |f (a + h) - f a - f' a * h| ≤ M * h ^ 2 := by
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have hlt : a + h < a := by linarith
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => hderiv x)
    have hsub : a - (a + h) = -h := by ring
    rw [hsub, eq_div_iff (by linarith : -h ≠ 0)] at hslope
    have hdiff : f (a + h) - f a = f' c * h := by linarith
    rw [hdiff, show f' c * h - f' a * h = (f' c - f' a) * h by ring, abs_mul]
    have hca : |c - a| ≤ |h| := by
      rw [abs_le]; constructor <;> linarith [hc.1, hc.2, abs_of_neg hh]
    calc |f' c - f' a| * |h| ≤ (M * |c - a|) * |h| :=
          mul_le_mul_of_nonneg_right (hlip c a) (abs_nonneg h)
      _ ≤ (M * |h|) * |h| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hca hM) (abs_nonneg h)
      _ = M * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  · simp
  · have hlt : a < a + h := by linarith
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => hderiv x)
    have hsub : a + h - a = h := by ring
    rw [hsub, eq_div_iff hh.ne'] at hslope
    have hdiff : f (a + h) - f a = f' c * h := by linarith
    rw [hdiff, show f' c * h - f' a * h = (f' c - f' a) * h by ring, abs_mul]
    have hca : |c - a| ≤ |h| := by
      rw [abs_le]; constructor <;> linarith [hc.1, hc.2, abs_of_pos hh]
    calc |f' c - f' a| * |h| ≤ (M * |c - a|) * |h| :=
          mul_le_mul_of_nonneg_right (hlip c a) (abs_nonneg h)
      _ ≤ (M * |h|) * |h| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hca hM) (abs_nonneg h)
      _ = M * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Global Lipschitz bound from a uniform derivative bound via the Mean Value Theorem. -/
lemma lip_of_deriv_bound {f f' : ℝ → ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hbd : ∀ x, |f' x| ≤ L) (x y : ℝ) :
    |f x - f y| ≤ L * |x - y| := by
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hderiv t)
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hslope
    have h1 : |f x - f y| = |f' c| * |x - y| := by
      rw [abs_sub_comm, abs_sub_comm x y, ← abs_mul, show f' c * (y - x) = f y - f x from hslope]
    rw [h1]; exact mul_le_mul_of_nonneg_right (hbd c) (abs_nonneg _)
  · simp
  · obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hderiv t)
    rw [eq_div_iff (sub_ne_zero.mpr hgt.ne')] at hslope
    have h1 : |f x - f y| = |f' c| * |x - y| := by
      rw [← abs_mul, show f' c * (x - y) = f x - f y from hslope]
    rw [h1]; exact mul_le_mul_of_nonneg_right (hbd c) (abs_nonneg _)

/-- Smooth proximal map `ψ_λ(z) = (√((z+1)^2 + λ) - √((z-1)^2 + λ)) / 2 : ℝ → (-1, 1)`. -/
noncomputable def psi (lam z : ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt ((z + 1) ^ 2 + lam) - Real.sqrt ((z - 1) ^ 2 + lam))

noncomputable def psiDeriv (lam z : ℝ) : ℝ :=
  (1 / 2) * ((z + 1) / Real.sqrt ((z + 1) ^ 2 + lam) - (z - 1) / Real.sqrt ((z - 1) ^ 2 + lam))

/-- Exact closed-form inverse `h_λ(u) = u √(1 + λ / (1 - u^2))` of `ψ_λ` on `(-1, 1)`. -/
noncomputable def hInv (lam u : ℝ) : ℝ :=
  u * Real.sqrt (1 + lam / (1 - u ^ 2))

lemma psi_neg (lam z : ℝ) : psi lam (-z) = -psi lam z := by
  unfold psi
  have h1 : (-z + 1) ^ 2 + lam = (z - 1) ^ 2 + lam := by ring
  have h2 : (-z - 1) ^ 2 + lam = (z + 1) ^ 2 + lam := by ring
  rw [h1, h2]; ring

lemma abs_psi_lt_one {lam : ℝ} (hlam : 0 < lam) (z : ℝ) : |psi lam z| < 1 := by
  unfold psi
  set a := Real.sqrt ((z + 1) ^ 2 + lam)
  set b := Real.sqrt ((z - 1) ^ 2 + lam)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha_gt : |z + 1| < a := by
    have h1 : |z + 1| ^ 2 < a ^ 2 := by
      rw [sq_abs, Real.sq_sqrt (by positivity)]; linarith
    nlinarith [h1, abs_nonneg (z + 1), ha]
  have hb_gt : |z - 1| < b := by
    have h1 : |z - 1| ^ 2 < b ^ 2 := by
      rw [sq_abs, Real.sq_sqrt (by positivity)]; linarith
    nlinarith [h1, abs_nonneg (z - 1), hb]
  have hdiff : (a - b) * (a + b) = 4 * z := by
    have h1 : a ^ 2 - b ^ 2 = 4 * z := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; ring
    linarith [h1]
  have hsum_gt : 2 * |z| < a + b := by
    have htri : 2 * |z| ≤ |z + 1| + |z - 1| := by
      have h1 := abs_add_le (z + 1) (z - 1)
      have h2 : (z + 1) + (z - 1) = 2 * z := by ring
      rw [h2, abs_mul, abs_of_pos two_pos] at h1
      exact h1
    linarith [htri, ha_gt, hb_gt]
  have hab : |a - b| * (a + b) = 4 * |z| := by
    have := congrArg abs hdiff
    rw [abs_mul, abs_of_pos (by linarith : 0 < a + b), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
    exact this
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hlt : |a - b| < 2 := by nlinarith [hab, hsum_gt, abs_nonneg (a - b), ha, hb]
  linarith

lemma hasDerivAt_sqrt_shift {lam : ℝ} (hlam : 0 < lam) (c z : ℝ) :
    HasDerivAt (fun t => Real.sqrt ((t + c) ^ 2 + lam))
      ((z + c) / Real.sqrt ((z + c) ^ 2 + lam)) z := by
  have hinner : HasDerivAt (fun t => (t + c) ^ 2 + lam) (2 * (z + c)) z := by
    have h1 : HasDerivAt (fun t => t + c) 1 z := (hasDerivAt_id z).add_const c
    have h2 : HasDerivAt (fun t => (t + c) ^ 2) (2 * (z + c) ^ 1 * 1) z := h1.pow 2
    exact (h2.add_const lam).congr_deriv (by ring)
  have hpos : (z + c) ^ 2 + lam ≠ 0 := (by positivity : 0 < (z + c) ^ 2 + lam).ne'
  exact (hinner.sqrt hpos).congr_deriv (by
    have hne : Real.sqrt ((z + c) ^ 2 + lam) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hne])

lemma hasDerivAt_psi {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    HasDerivAt (psi lam) (psiDeriv lam z) z := by
  have h1 := hasDerivAt_sqrt_shift hlam 1 z
  have h2 : HasDerivAt (fun t => Real.sqrt ((t - 1) ^ 2 + lam))
      ((z - 1) / Real.sqrt ((z - 1) ^ 2 + lam)) z := by
    simpa [sub_eq_add_neg] using hasDerivAt_sqrt_shift hlam (-1) z
  exact (h1.sub h2).const_mul (1 / 2)

lemma psiDeriv_bounds {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    0 < psiDeriv lam z ∧ psiDeriv lam z < 1 := by
  unfold psiDeriv
  let g : ℝ → ℝ := fun t => t / Real.sqrt (t ^ 2 + lam)
  have hg_lt : ∀ t, |g t| < 1 := fun t => by
    simp only [g, abs_div, abs_of_pos (Real.sqrt_pos.mpr (by positivity : 0 < t ^ 2 + lam))]
    rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
    have h1 : |t| ^ 2 < (Real.sqrt (t ^ 2 + lam)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt (by positivity)]; linarith
    nlinarith [h1, abs_nonneg t, Real.sqrt_nonneg (t ^ 2 + lam)]
  have hg_mono : ∀ a b, a < b → g a < g b := by
    intro a b hab
    have hderiv_g : ∀ t, HasDerivAt g (lam / (t ^ 2 + lam) / Real.sqrt (t ^ 2 + lam)) t := by
      intro t
      have hs := hasDerivAt_sqrt_shift hlam 0 t
      simp only [add_zero] at hs
      have hne : Real.sqrt (t ^ 2 + lam) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hq := (hasDerivAt_id t).div hs hne
      exact hq.congr_deriv (by
        simp only [id_eq]
        have hsq : Real.sqrt (t ^ 2 + lam) ^ 2 = t ^ 2 + lam := Real.sq_sqrt (by positivity)
        have hpos : t ^ 2 + lam ≠ 0 := (by positivity : 0 < t ^ 2 + lam).ne'
        field_simp [hne, hpos]
        nlinarith [hsq])
    obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope g
      (fun t => lam / (t ^ 2 + lam) / Real.sqrt (t ^ 2 + lam)) hab
      (fun t _ => (hderiv_g t).continuousAt.continuousWithinAt)
      (fun t _ => hderiv_g t)
    have hpos_d : 0 < lam / (c ^ 2 + lam) / Real.sqrt (c ^ 2 + lam) := by positivity
    rw [hslope] at hpos_d
    exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hab)).mp hpos_d)
  constructor
  · have hlt := hg_mono (z - 1) (z + 1) (by linarith)
    simp only [g] at hlt
    linarith
  · have h1 := (abs_lt.mp (hg_lt (z + 1))).2
    have h2 := (abs_lt.mp (hg_lt (z - 1))).1
    simp only [g] at h1 h2
    linarith

lemma psiDeriv_lip {lam : ℝ} (hlam : 0 < lam) (x y : ℝ) :
    |psiDeriv lam x - psiDeriv lam y| ≤ (1 / Real.sqrt lam) * |x - y| := by
  let g : ℝ → ℝ := fun t => t / Real.sqrt (t ^ 2 + lam)
  let g' : ℝ → ℝ := fun t => lam / (t ^ 2 + lam) / Real.sqrt (t ^ 2 + lam)
  have hdg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have hs := hasDerivAt_sqrt_shift hlam 0 t
    simp only [add_zero] at hs
    have hne : Real.sqrt (t ^ 2 + lam) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hq := (hasDerivAt_id t).div hs hne
    exact hq.congr_deriv (by
      simp only [g', id_eq]
      have hsq : Real.sqrt (t ^ 2 + lam) ^ 2 = t ^ 2 + lam := Real.sq_sqrt (by positivity)
      have hpos : t ^ 2 + lam ≠ 0 := (by positivity : 0 < t ^ 2 + lam).ne'
      field_simp [hne, hpos]
      nlinarith [hsq])
  have hg'_bd : ∀ t, |g' t| ≤ 1 / Real.sqrt lam := by
    intro t
    have hpos : 0 < g' t := by simp only [g']; positivity
    rw [abs_of_pos hpos]
    simp only [g']
    have h1 : lam / (t ^ 2 + lam) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [sq_nonneg t])
    have h2 : Real.sqrt lam ≤ Real.sqrt (t ^ 2 + lam) := Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
    have h3 : 1 / Real.sqrt (t ^ 2 + lam) ≤ 1 / Real.sqrt lam :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr hlam) h2
    calc lam / (t ^ 2 + lam) / Real.sqrt (t ^ 2 + lam)
        = (lam / (t ^ 2 + lam)) * (1 / Real.sqrt (t ^ 2 + lam)) := by ring
      _ ≤ 1 * (1 / Real.sqrt lam) := mul_le_mul h1 h3 (by positivity) zero_le_one
      _ = 1 / Real.sqrt lam := one_mul _
  have hglip := lip_of_deriv_bound (by positivity : 0 ≤ 1 / Real.sqrt lam) hdg hg'_bd
  have heq : psiDeriv lam x - psiDeriv lam y =
      (1 / 2) * ((g (x + 1) - g (y + 1)) - (g (x - 1) - g (y - 1))) := by
    simp only [psiDeriv, g]; ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have htri := abs_sub (g (x + 1) - g (y + 1)) (g (x - 1) - g (y - 1))
  have h1 := hglip (x + 1) (y + 1)
  have h2 := hglip (x - 1) (y - 1)
  have hs1 : (x + 1) - (y + 1) = x - y := by ring
  have hs2 : (x - 1) - (y - 1) = x - y := by ring
  rw [hs1] at h1; rw [hs2] at h2
  linarith [htri, h1, h2]

lemma psi_taylor {lam : ℝ} (hlam : 0 < lam) (a h : ℝ) :
    |psi lam (a + h) - psi lam a - psiDeriv lam a * h| ≤ (1 / Real.sqrt lam) * h ^ 2 :=
  taylor_of_deriv_lip (by positivity) (hasDerivAt_psi hlam) (psiDeriv_lip hlam) a h

lemma psi_lip {lam : ℝ} (hlam : 0 < lam) (x y : ℝ) : |psi lam x - psi lam y| ≤ |x - y| := by
  have h := lip_of_deriv_bound zero_le_one (hasDerivAt_psi hlam)
    (fun t => by
      have hb := psiDeriv_bounds hlam t
      rw [abs_of_pos hb.1]; exact hb.2.le) x y
  simpa using h

lemma psi_hInv {lam u : ℝ} (hlam : 0 < lam) (hu : |u| < 1) : psi lam (hInv lam u) = u := by
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu]
  set s := Real.sqrt (1 + lam / (1 - u ^ 2))
  have hs_gt1 : 1 < s := by
    have h1 : 1 ^ 2 < s ^ 2 := by
      rw [one_pow, Real.sq_sqrt (by positivity)]
      have : 0 < lam / (1 - u ^ 2) := div_pos hlam hu2
      linarith
    nlinarith [h1, Real.sqrt_nonneg (1 + lam / (1 - u ^ 2))]
  have hs_sq : s ^ 2 = 1 + lam / (1 - u ^ 2) := Real.sq_sqrt (by positivity)
  have hsq1 : (u * s + 1) ^ 2 + lam = (s + u) ^ 2 := by
    have hmul : (1 - u ^ 2) * s ^ 2 = 1 - u ^ 2 + lam := by
      rw [hs_sq]; field_simp
    nlinarith [hmul]
  have hsq2 : (u * s - 1) ^ 2 + lam = (s - u) ^ 2 := by
    have hmul : (1 - u ^ 2) * s ^ 2 = 1 - u ^ 2 + lam := by
      rw [hs_sq]; field_simp
    nlinarith [hmul]
  have hpos1 : 0 ≤ s + u := by linarith [(abs_lt.mp hu).1, hs_gt1]
  have hpos2 : 0 ≤ s - u := by linarith [(abs_lt.mp hu).2, hs_gt1]
  simp only [psi, hInv]
  change (1 / 2) * (Real.sqrt ((u * s + 1) ^ 2 + lam) - Real.sqrt ((u * s - 1) ^ 2 + lam)) = u
  rw [hsq1, hsq2, Real.sqrt_sq hpos1, Real.sqrt_sq hpos2]
  ring

lemma hInv_psi {lam : ℝ} (hlam : 0 < lam) (z : ℝ) : hInv lam (psi lam z) = z := by
  have hstrict : StrictMono (psi lam) :=
    strictMono_of_deriv_pos fun t => by
      rw [(hasDerivAt_psi hlam t).deriv]; exact (psiDeriv_bounds hlam t).1
  exact hstrict.injective (psi_hInv hlam (abs_psi_lt_one hlam z))

lemma hInv_sub_pos {lam u : ℝ} (hlam : 0 < lam) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < hInv lam u - u := by
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith
  have hs : 1 < Real.sqrt (1 + lam / (1 - u ^ 2)) := by
    have h1 : 1 ^ 2 < (Real.sqrt (1 + lam / (1 - u ^ 2))) ^ 2 := by
      rw [one_pow, Real.sq_sqrt (by positivity)]
      have : 0 < lam / (1 - u ^ 2) := div_pos hlam hu2
      linarith
    nlinarith [h1, Real.sqrt_nonneg (1 + lam / (1 - u ^ 2))]
  simp only [hInv]; nlinarith

lemma hInv_sub_neg {lam u : ℝ} (hlam : 0 < lam) (hu1 : -1 < u) (hu0 : u < 0) :
    hInv lam u - u < 0 := by
  have h := hInv_sub_pos hlam (neg_pos.mpr hu0) (by linarith)
  simp only [hInv, neg_sq] at h ⊢
  linarith

lemma abs_hInv_sub_le {lam γ u : ℝ} (hlam : 0 < lam) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : |u| ≤ 1 - γ / 2) :
    |hInv lam u - u| ≤ 4 * lam / γ := by
  have hu_lt : |u| < 1 := by linarith
  have hu2_ge : γ / 2 ≤ 1 - u ^ 2 := by
    have h1 : u ^ 2 ≤ (1 - γ / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg u) hu 2
    nlinarith [h1, hγ0, hγ1]
  have hs_ge1 : 1 ≤ Real.sqrt (1 + lam / (1 - u ^ 2)) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [div_pos hlam (by linarith : 0 < 1 - u ^ 2)])
  have hs_sub : Real.sqrt (1 + lam / (1 - u ^ 2)) - 1 ≤ lam / (1 - u ^ 2) := by
    have h1 : (Real.sqrt (1 + lam / (1 - u ^ 2)) - 1) * (Real.sqrt (1 + lam / (1 - u ^ 2)) + 1) =
        lam / (1 - u ^ 2) := by
      have hsq : (Real.sqrt (1 + lam / (1 - u ^ 2))) ^ 2 = 1 + lam / (1 - u ^ 2) :=
        Real.sq_sqrt (by linarith [div_pos hlam (by linarith : 0 < 1 - u ^ 2)])
      linarith [hsq]
    nlinarith [h1, hs_ge1]
  have hdiv_le : lam / (1 - u ^ 2) ≤ 2 * lam / γ := by
    rw [div_le_div_iff₀ (by linarith) hγ0]
    nlinarith [hu2_ge, hlam]
  have heq : hInv lam u - u = u * (Real.sqrt (1 + lam / (1 - u ^ 2)) - 1) := by
    simp only [hInv]; ring
  rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs_ge1)]
  calc |u| * (Real.sqrt (1 + lam / (1 - u ^ 2)) - 1)
      ≤ 1 * (2 * lam / γ) := mul_le_mul hu_lt.le (hs_sub.trans hdiv_le) (sub_nonneg.mpr hs_ge1) zero_le_one
    _ ≤ 4 * lam / γ := by rw [one_mul]; exact div_le_div_of_nonneg_right (by linarith) hγ0.le

/-- Antiderivative helper for the convex barrier `R_bar`. -/
noncomputable def G_bar (lam w : ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt (w * (w + lam)) + lam * Real.log (Real.sqrt w + Real.sqrt (w + lam)))

/-- Convex barrier `R_bar` on `(-1, 1)` with `R_bar'(u) = (hInv lam u - u) / η`. -/
noncomputable def R_bar (lam η u : ℝ) : ℝ :=
  (1 / η) * (G_bar lam 1 - G_bar lam (1 - u ^ 2) - u ^ 2 / 2)

lemma hasDerivAt_G_bar {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    HasDerivAt (G_bar lam) ((1 / 2) * Real.sqrt (1 + lam / w)) w := by
  have hwl : 0 < w + lam := by linarith
  have hprod_pos : 0 < w * (w + lam) := mul_pos hw hwl
  have hd1 : HasDerivAt (fun t => Real.sqrt (t * (t + lam)))
      ((2 * w + lam) / (2 * Real.sqrt (w * (w + lam)))) w := by
    have hp : HasDerivAt (fun t => t * (t + lam)) (2 * w + lam) w :=
      ((hasDerivAt_id w).mul ((hasDerivAt_id w).add_const lam)).congr_deriv (by simp only [id_eq]; ring)
    exact hp.sqrt hprod_pos.ne'
  have hd2 : HasDerivAt (fun t => Real.sqrt t + Real.sqrt (t + lam))
      (1 / (2 * Real.sqrt w) + 1 / (2 * Real.sqrt (w + lam))) w := by
    have ha := (hasDerivAt_id w).sqrt hw.ne'
    have hb := ((hasDerivAt_id w).add_const lam).sqrt hwl.ne'
    exact ha.add hb
  have hsum_pos : 0 < Real.sqrt w + Real.sqrt (w + lam) :=
    add_pos (Real.sqrt_pos.mpr hw) (Real.sqrt_pos.mpr hwl)
  have hd3 := (hd2.log hsum_pos.ne').const_mul lam
  have hd_all := (hd1.add hd3).const_mul (1 / 2)
  exact hd_all.congr_deriv (by
    have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
    have hswl : 0 < Real.sqrt (w + lam) := Real.sqrt_pos.mpr hwl
    have hmul_sq : Real.sqrt (w * (w + lam)) = Real.sqrt w * Real.sqrt (w + lam) :=
      Real.sqrt_mul hw.le (w + lam)
    have hrat_sq : Real.sqrt (1 + lam / w) = Real.sqrt (w + lam) / Real.sqrt w := by
      rw [← Real.sqrt_div hwl.le]; congr 1; field_simp
    rw [hmul_sq, hrat_sq]
    have hsq1 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
    have hsq2 : Real.sqrt (w + lam) ^ 2 = w + lam := Real.sq_sqrt hwl.le
    have hne1 : Real.sqrt w ≠ 0 := hsw.ne'
    have hne2 : Real.sqrt (w + lam) ≠ 0 := hswl.ne'
    have hne3 : Real.sqrt w + Real.sqrt (w + lam) ≠ 0 := hsum_pos.ne'
    field_simp [hne1, hne2, hne3]
    nlinarith [hsq1, hsq2])

lemma hasDerivAt_R_bar {lam η u : ℝ} (hlam : 0 < lam) (hu : |u| < 1) :
    HasDerivAt (R_bar lam η) ((hInv lam u - u) / η) u := by
  have hw : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu]
  have hG := hasDerivAt_G_bar hlam hw
  have hinner : HasDerivAt (fun t => 1 - t ^ 2) (-2 * u) u :=
    ((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).congr_deriv (by simp only [id_eq]; ring)
  have hcomp : HasDerivAt (G_bar lam ∘ fun t => 1 - t ^ 2)
      ((1 / 2) * Real.sqrt (1 + lam / (1 - u ^ 2)) * (-2 * u)) u :=
    hG.comp u hinner
  have hsq : HasDerivAt (fun t => t ^ 2 / 2) u u :=
    (((hasDerivAt_id u).pow 2).div_const 2).congr_deriv (by simp only [id_eq]; ring)
  have hall := (((hasDerivAt_const u (G_bar lam 1)).sub hcomp).sub hsq).const_mul (1 / η)
  exact hall.congr_deriv (by simp only [hInv]; ring)

lemma hInv_sub_mono {lam : ℝ} (hlam : 0 < lam) {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) (hab : a ≤ b) :
    hInv lam a - a ≤ hInv lam b - b := by
  let f : ℝ → ℝ := fun u => u * (Real.sqrt (1 + lam / (1 - u ^ 2)) - 1)
  have hf_eq : ∀ u, hInv lam u - u = f u := fun u => by simp only [hInv, f]; ring
  rw [hf_eq, hf_eq]
  have hf_nonneg : ∀ u, 0 ≤ u → u < 1 → 0 ≤ f u := fun u hu0 hu1 => by
    have h1 : 1 ≤ Real.sqrt (1 + lam / (1 - u ^ 2)) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by
        have : 0 < 1 - u ^ 2 := by nlinarith
        linarith [div_pos hlam this])
    exact mul_nonneg hu0 (by linarith)
  have hf_mono_nn : ∀ x y, 0 ≤ x → x ≤ y → y < 1 → f x ≤ f y := fun x y hx0 hxy hy1 => by
    have h1x : 0 < 1 - x ^ 2 := by nlinarith
    have h1y : 0 < 1 - y ^ 2 := by nlinarith
    have hsq_le : 1 - y ^ 2 ≤ 1 - x ^ 2 := by nlinarith
    have hdiv : lam / (1 - x ^ 2) ≤ lam / (1 - y ^ 2) :=
      div_le_div_of_nonneg_left hlam.le h1y hsq_le
    have hs : Real.sqrt (1 + lam / (1 - x ^ 2)) ≤ Real.sqrt (1 + lam / (1 - y ^ 2)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs1 : 1 ≤ Real.sqrt (1 + lam / (1 - x ^ 2)) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [div_pos hlam h1x])
    exact mul_le_mul hxy (by linarith) (by linarith) (by linarith)
  have hf_neg : ∀ u, f (-u) = -f u := fun u => by simp only [f, neg_sq]; ring
  rcases le_or_gt 0 a with ha0 | ha0
  · exact hf_mono_nn a b ha0 hab (abs_lt.mp hb).2
  · rcases le_or_gt 0 b with hb0 | hb0
    · have h1 : f a ≤ 0 := by
        have := hf_nonneg (-a) (by linarith) (by linarith [(abs_lt.mp ha).1])
        rw [hf_neg] at this; linarith
      exact h1.trans (hf_nonneg b hb0 (abs_lt.mp hb).2)
    · have h1 := hf_mono_nn (-b) (-a) (by linarith) (by linarith) (by linarith [(abs_lt.mp ha).1])
      rw [hf_neg, hf_neg] at h1; linarith

lemma R_bar_convex_ineq {lam η x u : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hx : |x| < 1) (hu : |u| < 1) :
    ((hInv lam u - u) / η) * (x - u) ≤ R_bar lam η x - R_bar lam η u := by
  rcases lt_trichotomy u x with hlt | rfl | hgt
  · have hmem : ∀ t ∈ Set.Icc u x, |t| < 1 := fun t ht => by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, (abs_lt.mp hx).2, (abs_lt.mp hu).1]
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (R_bar lam η) (fun t => (hInv lam t - t) / η) hlt
      (fun t ht => (hasDerivAt_R_bar hlam (hmem t ht)).continuousAt.continuousWithinAt)
      (fun t ht => hasDerivAt_R_bar hlam (hmem t ⟨ht.1.le, ht.2.le⟩))
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hslope
    have hmono := hInv_sub_mono hlam hu (hmem c ⟨hc.1.le, hc.2.le⟩) hc.1.le
    have hdiv : (hInv lam u - u) / η ≤ (hInv lam c - c) / η :=
      div_le_div_of_nonneg_right hmono hη.le
    rw [← hslope]
    exact mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hlt.le)
  · simp
  · have hmem : ∀ t ∈ Set.Icc x u, |t| < 1 := fun t ht => by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, (abs_lt.mp hx).1, (abs_lt.mp hu).2]
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (R_bar lam η) (fun t => (hInv lam t - t) / η) hgt
      (fun t ht => (hasDerivAt_R_bar hlam (hmem t ht)).continuousAt.continuousWithinAt)
      (fun t ht => hasDerivAt_R_bar hlam (hmem t ⟨ht.1.le, ht.2.le⟩))
    rw [eq_div_iff (sub_ne_zero.mpr hgt.ne')] at hslope
    have hmono := hInv_sub_mono hlam (hmem c ⟨hc.1.le, hc.2.le⟩) hu hc.2.le
    have hdiv : (hInv lam c - c) / η ≤ (hInv lam u - u) / η :=
      div_le_div_of_nonneg_right hmono hη.le
    have hmul : (hInv lam c - c) / η * (u - x) ≤ (hInv lam u - u) / η * (u - x) :=
      mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hgt.le)
    linarith [hslope, hmul]

lemma R_bar_bounds {lam η u : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 4) (hη : 0 < η) (hu : |u| < 1) :
    0 ≤ R_bar lam η u ∧ R_bar lam η u ≤ 2 / η := by
  constructor
  · have h0 := R_bar_convex_ineq hlam hη hu (by simp : |(0 : ℝ)| < 1)
    have hR0 : R_bar lam η 0 = 0 := by simp [R_bar]
    have hh0 : hInv lam 0 = 0 := by simp [hInv]
    rw [hR0, hh0] at h0
    simp only [sub_zero, zero_div, zero_mul] at h0
    exact h0
  · have hw : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu]
    have hG_ge : (1 / 2) * (lam * Real.log (Real.sqrt lam)) ≤ G_bar lam (1 - u ^ 2) := by
      simp only [G_bar]
      have h1 : 0 ≤ Real.sqrt ((1 - u ^ 2) * (1 - u ^ 2 + lam)) := Real.sqrt_nonneg _
      have h2 : Real.sqrt lam ≤ Real.sqrt (1 - u ^ 2) + Real.sqrt (1 - u ^ 2 + lam) := by
        have ha : Real.sqrt lam ≤ Real.sqrt (1 - u ^ 2 + lam) := Real.sqrt_le_sqrt (by linarith)
        linarith [Real.sqrt_nonneg (1 - u ^ 2)]
      have h3 : Real.log (Real.sqrt lam) ≤ Real.log (Real.sqrt (1 - u ^ 2) + Real.sqrt (1 - u ^ 2 + lam)) :=
        Real.log_le_log (Real.sqrt_pos.mpr hlam) h2
      nlinarith [h1, h3, hlam]
    have hG1_sub : G_bar lam 1 - (1 / 2) * (lam * Real.log (Real.sqrt lam)) ≤ 2 := by
      simp only [G_bar]
      have hdiff_log : Real.log (Real.sqrt 1 + Real.sqrt (1 + lam)) - Real.log (Real.sqrt lam) =
          Real.log ((1 + Real.sqrt (1 + lam)) / Real.sqrt lam) := by
        rw [Real.sqrt_one, ← Real.log_div (by positivity) (Real.sqrt_pos.mpr hlam).ne']
      have hlog_le : Real.log ((1 + Real.sqrt (1 + lam)) / Real.sqrt lam) ≤
          (1 + Real.sqrt (1 + lam)) / Real.sqrt lam := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (1 + Real.sqrt (1 + lam)) / Real.sqrt lam)]
      have hs1 : Real.sqrt (1 + lam) ≤ 5 / 4 := by
        have hsq : (Real.sqrt (1 + lam)) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
          rw [Real.sq_sqrt (by linarith)]; linarith
        nlinarith [hsq, Real.sqrt_nonneg (1 + lam)]
      have hlam_sq : Real.sqrt lam ≤ 1 / 2 := by
        have hsq : (Real.sqrt lam) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
          rw [Real.sq_sqrt hlam.le]; linarith
        nlinarith [hsq, Real.sqrt_nonneg lam]
      have hmul_log : lam * Real.log ((1 + Real.sqrt (1 + lam)) / Real.sqrt lam) ≤
          Real.sqrt lam * (1 + Real.sqrt (1 + lam)) := by
        have h1 := mul_le_mul_of_nonneg_left hlog_le hlam.le
        have h2 : lam * ((1 + Real.sqrt (1 + lam)) / Real.sqrt lam) =
            Real.sqrt lam * (1 + Real.sqrt (1 + lam)) := by
          have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
          have hne : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
          field_simp; linarith [hsq]
        linarith [h1, h2]
      have hbound1 : Real.sqrt lam * (1 + Real.sqrt (1 + lam)) ≤ (1 / 2) * (9 / 4) := by
        nlinarith [hlam_sq, hs1, Real.sqrt_nonneg lam, Real.sqrt_nonneg (1 + lam)]
      have hprod : Real.sqrt (1 * (1 + lam)) ≤ 5 / 4 := by simpa using hs1
      have hcomb : Real.sqrt (1 * (1 + lam)) +
          lam * (Real.log (Real.sqrt 1 + Real.sqrt (1 + lam)) - Real.log (Real.sqrt lam)) ≤ 5 / 4 + 9 / 8 := by
        rw [hdiff_log]; linarith [hprod, hmul_log, hbound1]
      linarith [hcomb]
    simp only [R_bar]
    have hu2_nn : 0 ≤ u ^ 2 / 2 := by positivity
    have hnum : G_bar lam 1 - G_bar lam (1 - u ^ 2) - u ^ 2 / 2 ≤ 2 := by linarith [hG_ge, hG1_sub]
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hnum hη.le

/-- Exact pointwise barrier drift bound for a kick inside `[-(1 - γ/2), 1 - γ/2]`. -/
lemma R_bar_sub_le_of_interior {lam η γ x y : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hx : |x| ≤ 1 - γ / 2) (hy : |y| ≤ 1 - γ / 2) :
    |R_bar lam η y - R_bar lam η x| ≤ (4 * lam / (η * γ)) * |y - x| := by
  have hmem : ∀ t, (min x y ≤ t ∧ t ≤ max x y) → |t| ≤ 1 - γ / 2 := fun t ht => by
    rw [abs_le]
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    have hlo : -(1 - γ / 2) ≤ min x y := le_min hx'.1 hy'.1
    have hhi : max x y ≤ 1 - γ / 2 := max_le hx'.2 hy'.2
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hbd : ∀ t, |t| ≤ 1 - γ / 2 → |(hInv lam t - t) / η| ≤ 4 * lam / (η * γ) := fun t ht => by
    rw [abs_div, abs_of_pos hη]
    calc |hInv lam t - t| / η ≤ (4 * lam / γ) / η :=
          div_le_div_of_nonneg_right (abs_hInv_sub_le hlam hγ0 hγ1 ht) hη.le
      _ = 4 * lam / (η * γ) := by rw [div_div, mul_comm γ η]
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (R_bar lam η) (fun t => (hInv lam t - t) / η) hlt
      (fun t ht => (hasDerivAt_R_bar hlam (lt_of_le_of_lt (hmem t ⟨by rw [min_eq_left hlt.le]; exact ht.1,
        by rw [max_eq_right hlt.le]; exact ht.2⟩) (by linarith))).continuousAt.continuousWithinAt)
      (fun t ht => hasDerivAt_R_bar hlam (lt_of_le_of_lt (hmem t ⟨by rw [min_eq_left hlt.le]; exact ht.1.le,
        by rw [max_eq_right hlt.le]; exact ht.2.le⟩) (by linarith)))
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hslope
    rw [← hslope, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbd c (hmem c ⟨by rw [min_eq_left hlt.le]; exact hc.1.le,
      by rw [max_eq_right hlt.le]; exact hc.2.le⟩)) (abs_nonneg _)
  · simp
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (R_bar lam η) (fun t => (hInv lam t - t) / η) hgt
      (fun t ht => (hasDerivAt_R_bar hlam (lt_of_le_of_lt (hmem t ⟨by rw [min_eq_right hgt.le]; exact ht.1,
        by rw [max_eq_left hgt.le]; exact ht.2⟩) (by linarith))).continuousAt.continuousWithinAt)
      (fun t ht => hasDerivAt_R_bar hlam (lt_of_le_of_lt (hmem t ⟨by rw [min_eq_right hgt.le]; exact ht.1.le,
        by rw [max_eq_left hgt.le]; exact ht.2.le⟩) (by linarith)))
    rw [eq_div_iff (sub_ne_zero.mpr hgt.ne')] at hslope
    rw [abs_sub_comm, ← hslope, abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (hbd c (hmem c ⟨by rw [min_eq_right hgt.le]; exact hc.1.le,
      by rw [max_eq_left hgt.le]; exact hc.2.le⟩)) (abs_nonneg _)

/-- Exact proximal ascent inequality when `‖A / √n‖_op ≤ 20` and `η = 1 / 20`. -/
lemma prox_ascent_step {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (ω : EdgeIdx n → Bool)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    let η : ℝ := 1 / 20
    let y : Fin n → ℝ := fun i => (∑ j : Fin n, adjSign ω i j * x j) / Real.sqrt (n : ℝ)
    let x' : Fin n → ℝ := fun i => psi lam (x i + η * y i)
    let E : (Fin n → ℝ) → ℝ := fun z =>
      (∑ i : Fin n, ∑ j : Fin n, z i * adjSign ω i j * z j) / (2 * Real.sqrt (n : ℝ)) -
        ∑ i : Fin n, R_bar lam η (z i)
    10 * ∑ i : Fin n, (x' i - x i) ^ 2 ≤ E x' - E x := by
  intro η y x' E
  have hη : 0 < η := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hx' : ∀ i, |x' i| < 1 := fun i => abs_psi_lt_one hlam _
  -- Step 1: exact quadratic expansion of `(1 / (2 √n)) z^T A z`.
  have hquad : (∑ i : Fin n, ∑ j : Fin n, x' i * adjSign ω i j * x' j) / (2 * Real.sqrt (n : ℝ)) -
      (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) / (2 * Real.sqrt (n : ℝ)) =
      (∑ i : Fin n, y i * (x' i - x i)) +
      (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * (x' j - x j)) /
        (2 * Real.sqrt (n : ℝ)) := by
    have hsym : ∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j =
        ∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * (x' j - x j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [adjSign_symm]; ring
    have hexp : (∑ i : Fin n, ∑ j : Fin n, x' i * adjSign ω i j * x' j) -
        (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) =
        2 * (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j) +
        (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * (x' j - x j)) := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n, x' i * adjSign ω i j * x' j) -
          (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) =
          (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j) +
          (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * (x' j - x j)) +
          (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * (x' j - x j)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith [h1, hsym]
    have hlin_y : (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j) / Real.sqrt (n : ℝ) =
        ∑ i : Fin n, y i * (x' i - x i) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [y]
      rw [div_mul_eq_mul_div, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [← sub_div, hexp, add_div]
    have h2div : 2 * (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j) /
        (2 * Real.sqrt (n : ℝ)) =
        (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * x j) / Real.sqrt (n : ℝ) := by
      field_simp
    rw [h2div, hlin_y]
  -- Step 2: operator-norm bound on the quadratic term `≥ -10 ∑ (x' i - x i)^2`.
  have hcurv : -10 * ∑ i : Fin n, (x' i - x i) ^ 2 ≤
      (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * (x' j - x j)) /
        (2 * Real.sqrt (n : ℝ)) := by
    set S2 := ∑ i : Fin n, (x' i - x i) ^ 2
    by_cases hS0 : S2 = 0
    · have hz : ∀ i, x' i - x i = 0 := fun i => by
        have h1 : (x' i - x i) ^ 2 ≤ 0 :=
          (Finset.single_le_sum (f := fun k => (x' k - x k) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans hS0.le
        nlinarith
      simp [hz, hS0]
    · have hSpos : 0 < S2 := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hS0)
      let d : Fin n → ℝ := fun i => (x' i - x i) / Real.sqrt S2
      have hd_norm : ∑ i : Fin n, (d i) ^ 2 ≤ 1 := by
        simp only [d, div_pow, Real.sq_sqrt hSpos.le, ← Finset.sum_div]
        rw [div_self hSpos.ne']
      have hopd := hop d d hd_norm hd_norm
      have hscale : (∑ i : Fin n, ∑ j : Fin n, (x' i - x i) * adjSign ω i j * (x' j - x j)) =
          S2 * (∑ i : Fin n, ∑ j : Fin n, d i * adjSign ω i j * d j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : d i * adjSign ω i j * d j =
            (x' i - x i) * adjSign ω i j * (x' j - x j) / S2 := by
          simp only [d]
          have hsq : Real.sqrt S2 * Real.sqrt S2 = S2 := Real.mul_self_sqrt hSpos.le
          have hne : Real.sqrt S2 ≠ 0 := (Real.sqrt_pos.mpr hSpos).ne'
          field_simp [hne, hSpos.ne']
          rw [mul_assoc, mul_assoc]
          have hmul : (x' i - x i) * (adjSign ω i j * (x' j - x j)) * S2 =
              (x' i - x i) * (adjSign ω i j * (x' j - x j)) * (Real.sqrt S2 * Real.sqrt S2) := by rw [hsq]
          nlinarith only [hmul]
        rw [h1, mul_div_cancel₀ _ hSpos.ne']
      rw [hscale, mul_div_assoc]
      have hlo : -10 ≤ (∑ i : Fin n, ∑ j : Fin n, d i * adjSign ω i j * d j) / (2 * Real.sqrt (n : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have := (abs_le.mp hopd).1
        linarith
      have hmul := mul_le_mul_of_nonneg_left hlo hSpos.le
      linarith
  -- Step 3: barrier convexity gives `R_bar(x i) - R_bar(x' i) ≥ ((hInv(x' i) - x' i) / η) * (x i - x' i)`.
  have hbar : ∑ i : Fin n, (y i * (x' i - x i) - (R_bar lam η (x' i) - R_bar lam η (x i))) ≥
      20 * ∑ i : Fin n, (x' i - x i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hconv := R_bar_convex_ineq hlam hη (hx i) (hx' i)
    have hinv : hInv lam (x' i) = x i + η * y i := hInv_psi hlam (x i + η * y i)
    have hstat : y i - (hInv lam (x' i) - x' i) / η = 20 * (x' i - x i) := by
      rw [hinv]; simp only [η]; field_simp; ring
    have hmul : (y i - (hInv lam (x' i) - x' i) / η) * (x' i - x i) = 20 * (x' i - x i) ^ 2 := by
      rw [hstat]; ring
    linarith [hconv, hmul,
      show (hInv lam (x' i) - x' i) / η * (x i - x' i) =
        -((hInv lam (x' i) - x' i) / η * (x' i - x i)) by ring]
  have hE_diff : E x' - E x =
      ((∑ i : Fin n, ∑ j : Fin n, x' i * adjSign ω i j * x' j) / (2 * Real.sqrt (n : ℝ)) -
        (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) / (2 * Real.sqrt (n : ℝ))) -
      ∑ i : Fin n, (R_bar lam η (x' i) - R_bar lam η (x i)) := by
    simp only [E, Finset.sum_sub_distrib]; ring
  rw [hE_diff, hquad]
  have hsum_sub : (∑ i : Fin n, y i * (x' i - x i)) -
      ∑ i : Fin n, (R_bar lam η (x' i) - R_bar lam η (x i)) =
      ∑ i : Fin n, (y i * (x' i - x i) - (R_bar lam η (x' i) - R_bar lam η (x i))) := by
    rw [← Finset.sum_sub_distrib]
  linarith [hsum_sub, hbar, hcurv]

/-- Degree-5 Hermite smoothstep polynomial `1 - 10 s^3 + 15 s^4 - 6 s^5` clamped to `[0, 1]`. -/
noncomputable def hermiteStep (s : ℝ) : ℝ :=
  if s ≤ 0 then 1 else if 1 ≤ s then 0 else 1 - 10 * s ^ 3 + 15 * s ^ 4 - 6 * s ^ 5

noncomputable def hermiteStepDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else if 1 ≤ s then 0 else -30 * s ^ 2 * (1 - s) ^ 2

lemma hasDerivAt_hermiteStep (s : ℝ) : HasDerivAt hermiteStep (hermiteStepDeriv s) s := by
  let q : ℝ → ℝ := fun t => 1 - 10 * t ^ 3 + 15 * t ^ 4 - 6 * t ^ 5
  let q' : ℝ → ℝ := fun t => -30 * t ^ 2 * (1 - t) ^ 2
  have hq : ∀ t, HasDerivAt q (q' t) t := fun t => by
    have h1 := ((hasDerivAt_const t (1 : ℝ)).sub (((hasDerivAt_id t).pow 3).const_mul 10)).add
      (((hasDerivAt_id t).pow 4).const_mul 15) |>.sub (((hasDerivAt_id t).pow 5).const_mul 6)
    exact h1.congr_deriv (by simp only [q', id_eq]; ring)
  rcases lt_trichotomy s 0 with hneg | rfl | hpos
  · have hev : hermiteStep =ᶠ[nhds s] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_lt_nhds hneg] with t ht
      simp [hermiteStep, ht.le]
    simpa [hermiteStepDeriv, hneg.le] using (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq hev
  · rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨min (1 / 2) (Real.sqrt (ε / 32)), lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity)),
      fun t htne ht => ?_⟩
    simp only [hermiteStepDeriv, le_refl, ite_true, slope_def_field, sub_zero,
      Real.dist_eq] at ht ⊢
    rw [show hermiteStep 0 = 1 by simp [hermiteStep]]
    rcases le_or_gt t 0 with ht0 | ht0
    · simp [hermiteStep, ht0, hε]
    · have ht1 : t < 1 := by
        have hlt_min : t < min (1 / 2) (Real.sqrt (ε / 32)) := (abs_lt.mp ht).2
        linarith [hlt_min, min_le_left (1 / 2 : ℝ) (Real.sqrt (ε / 32))]
      have hne : ¬ t ≤ 0 := not_le.mpr ht0
      have hne1 : ¬ 1 ≤ t := not_le.mpr ht1
      simp only [hermiteStep, if_neg hne, if_neg hne1]
      have hsimp : (1 - 10 * t ^ 3 + 15 * t ^ 4 - 6 * t ^ 5 - 1) / t =
          t ^ 2 * (-10 + 15 * t - 6 * t ^ 2) := by
        have ht0' : t ≠ 0 := ht0.ne'
        field_simp [ht0']; ring
      rw [hsimp, abs_mul, abs_of_nonneg (sq_nonneg t)]
      have hpoly : |-10 + 15 * t - 6 * t ^ 2| ≤ 31 := by
        rw [abs_le]; constructor <;> nlinarith [ht0, ht1]
      have ht2 : t ^ 2 < ε / 32 := by
        have hlt_sq : |t| < Real.sqrt (ε / 32) := lt_of_lt_of_le ht (min_le_right _ _)
        have := pow_lt_pow_left₀ hlt_sq (abs_nonneg t) (by decide : 2 ≠ 0)
        rwa [sq_abs, Real.sq_sqrt (by positivity)] at this
      calc t ^ 2 * |-10 + 15 * t - 6 * t ^ 2| ≤ t ^ 2 * 31 :=
            mul_le_mul_of_nonneg_left hpoly (sq_nonneg t)
        _ < (ε / 32) * 31 := mul_lt_mul_of_pos_right ht2 (by norm_num)
        _ < ε := by linarith
  · rcases lt_trichotomy s 1 with hlt1 | rfl | hgt1
    · have hev : hermiteStep =ᶠ[nhds s] q := by
        filter_upwards [eventually_gt_nhds hpos, eventually_lt_nhds hlt1] with t ht0 ht1
        simp [hermiteStep, q, not_le.mpr ht0, not_le.mpr ht1]
      have hne0 : ¬ s ≤ 0 := not_le.mpr hpos
      have hne1 : ¬ 1 ≤ s := not_le.mpr hlt1
      simpa [hermiteStepDeriv, q', hne0, hne1] using (hq s).congr_of_eventuallyEq hev
    · rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      refine ⟨min (1 / 2) (Real.sqrt (ε / 32)), lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity)),
        fun t htne ht => ?_⟩
      have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num
      simp only [hermiteStepDeriv, if_neg h10, le_refl, ite_true, slope_def_field, sub_zero,
        Real.dist_eq] at ht ⊢
      rw [show hermiteStep 1 = 0 by simp [hermiteStep, h10], sub_zero]
      rcases le_or_gt 1 t with ht1 | ht1
      · have hne0 : ¬ t ≤ 0 := by linarith
        simp [hermiteStep, hne0, ht1, hε]
      · have ht0 : 0 < t := by
          have := (abs_lt.mp ht).1
          linarith [min_le_left (1 / 2) (Real.sqrt (ε / 32))]
        have hne0 : ¬ t ≤ 0 := not_le.mpr ht0
        have hne1 : ¬ 1 ≤ t := not_le.mpr ht1
        simp only [hermiteStep, if_neg hne0, if_neg hne1]
        have hsimp : (1 - 10 * t ^ 3 + 15 * t ^ 4 - 6 * t ^ 5) / (t - 1) =
            -(t - 1) ^ 2 * (1 + 3 * t + 6 * t ^ 2) := by
          have hne : t - 1 ≠ 0 := by linarith
          field_simp [hne]; ring
        rw [hsimp, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (t - 1))]
        have hpoly : |1 + 3 * t + 6 * t ^ 2| ≤ 10 := by
          rw [abs_le]; constructor <;> nlinarith [ht0, ht1]
        have ht2 : (t - 1) ^ 2 < ε / 32 := by
          have hlt_sq : |t - 1| < Real.sqrt (ε / 32) := lt_of_lt_of_le ht (min_le_right _ _)
          have := pow_lt_pow_left₀ hlt_sq (abs_nonneg _) (by decide : 2 ≠ 0)
          rwa [sq_abs, Real.sq_sqrt (by positivity)] at this
        calc (t - 1) ^ 2 * |1 + 3 * t + 6 * t ^ 2| ≤ (t - 1) ^ 2 * 10 :=
              mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
          _ < (ε / 32) * 10 := mul_lt_mul_of_pos_right ht2 (by norm_num)
          _ < ε := by linarith
    · have hev : hermiteStep =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hgt1] with t ht
        have hne0 : ¬ t ≤ 0 := by linarith
        simp [hermiteStep, hne0, ht.le]
      have hne0 : ¬ s ≤ 0 := by linarith
      simpa [hermiteStepDeriv, hne0, hgt1.le] using (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev

lemma hermiteStep_bounds (s : ℝ) : 0 ≤ hermiteStep s ∧ hermiteStep s ≤ 1 := by
  unfold hermiteStep
  split_ifs with h1 h2
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · push Not at h1 h2
    have hfac1 : 1 - 10 * s ^ 3 + 15 * s ^ 4 - 6 * s ^ 5 =
        (1 - s) ^ 3 * (1 + 3 * s + 6 * s ^ 2) := by ring
    have hfac2 : 1 - (1 - 10 * s ^ 3 + 15 * s ^ 4 - 6 * s ^ 5) =
        s ^ 3 * (10 - 15 * s + 6 * s ^ 2) := by ring
    have hp1 : 0 ≤ (1 - s) ^ 3 * (1 + 3 * s + 6 * s ^ 2) := by
      have ha : 0 ≤ (1 - s) ^ 3 := pow_nonneg (by linarith) 3
      have hb : 0 ≤ 1 + 3 * s + 6 * s ^ 2 := by nlinarith
      exact mul_nonneg ha hb
    have hp2 : 0 ≤ s ^ 3 * (10 - 15 * s + 6 * s ^ 2) := by
      have ha : 0 ≤ s ^ 3 := pow_nonneg h1.le 3
      have hb : 0 ≤ 10 - 15 * s + 6 * s ^ 2 := by nlinarith [sq_nonneg (s - 5 / 4)]
      exact mul_nonneg ha hb
    constructor <;> linarith [hfac1, hfac2, hp1, hp2]

lemma abs_hermiteStepDeriv_le (s : ℝ) : |hermiteStepDeriv s| ≤ 2 := by
  unfold hermiteStepDeriv
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · push Not at h1 h2
    have hprod : 0 ≤ s * (1 - s) ∧ s * (1 - s) ≤ 1 / 4 := ⟨by nlinarith, by nlinarith [sq_nonneg (s - 1 / 2)]⟩
    have hsq : s ^ 2 * (1 - s) ^ 2 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ hprod.1 hprod.2 2
      linarith [show (s * (1 - s)) ^ 2 = s ^ 2 * (1 - s) ^ 2 by ring,
        show ((1 / 4 : ℝ)) ^ 2 = 1 / 16 by norm_num]
    rw [abs_le]; constructor <;> nlinarith [hsq, sq_nonneg s, sq_nonneg (1 - s)]

lemma hermiteStepDeriv_lip (x y : ℝ) : |hermiteStepDeriv x - hermiteStepDeriv y| ≤ 10 * |x - y| := by
  let g : ℝ → ℝ := fun t => -30 * t ^ 2 * (1 - t) ^ 2
  have hg_lip : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |g a - g b| ≤ 10 * |a - b| := by
    intro a b ha0 ha1 hb0 hb1
    have hdg : ∀ t, HasDerivAt g (-60 * t * (1 - t) * (1 - 2 * t)) t := fun t => by
      have h1 := (((hasDerivAt_id t).pow 2).const_mul (-30)).mul
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2)
      exact h1.congr_deriv (by simp only [id_eq, Pi.sub_apply, Pi.pow_apply]; ring)
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |-60 * t * (1 - t) * (1 - 2 * t)| ≤ 10 := fun t ht => by
      have h1 : 0 ≤ t * (1 - t) ∧ t * (1 - t) ≤ 1 / 4 :=
        ⟨by nlinarith [ht.1, ht.2], by nlinarith [sq_nonneg (t - 1 / 2)]⟩
      -- Note `max_{t ∈ [0,1]} |t(1-t)(1-2t)| = 1/(6√3) < 1/10`, so `60 * ... < 6 ≤ 10`!
      have hsq : (t * (1 - t) * (1 - 2 * t)) ^ 2 ≤ 1 / 100 := by
        -- Let `u = t(1-t) ∈ [0, 1/4]`; `(1 - 2t)^2 = 1 - 4u`, so `u^2 (1 - 4u) ≤ 1/108 ≤ 1/100`!
        set u := t * (1 - t)
        have hu1 : (1 - 2 * t) ^ 2 = 1 - 4 * u := by simp only [u]; ring
        have heq : (t * (1 - t) * (1 - 2 * t)) ^ 2 = u ^ 2 * (1 - 4 * u) := by
          rw [mul_pow, hu1]
        rw [heq]
        have hcubic : u ^ 2 * (1 - 4 * u) ≤ 1 / 108 := by
          nlinarith [sq_nonneg (u - 1 / 6), h1.1, show 1 / 108 - u ^ 2 * (1 - 4 * u) =
            (u - 1 / 6) ^ 2 * (4 * u + 1 / 3) by ring]
        linarith
      rw [abs_le]
      have hsq60 : (-60 * t * (1 - t) * (1 - 2 * t)) ^ 2 ≤ 100 := by
        linarith [hsq, show (-60 * t * (1 - t) * (1 - 2 * t)) ^ 2 =
          3600 * (t * (1 - t) * (1 - 2 * t)) ^ 2 by ring]
      constructor <;> nlinarith [hsq60]
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
        (fun t => -60 * t * (1 - t) * (1 - 2 * t)) hlt
        (fun t _ => (hdg t).continuousAt.continuousWithinAt)
        (fun t _ => hdg t)
      rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hslope
      rw [abs_sub_comm, ← hslope, abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (hbd c ⟨by linarith [hc.1], by linarith [hc.2]⟩) (abs_nonneg _)
    · simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
        (fun t => -60 * t * (1 - t) * (1 - 2 * t)) hgt
        (fun t _ => (hdg t).continuousAt.continuousWithinAt)
        (fun t _ => hdg t)
      rw [eq_div_iff (sub_ne_zero.mpr hgt.ne')] at hslope
      rw [← hslope, abs_mul]
      exact mul_le_mul_of_nonneg_right (hbd c ⟨by linarith [hc.1], by linarith [hc.2]⟩) (abs_nonneg _)
  let cl : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hcl_eq : ∀ t, hermiteStepDeriv t = g (cl t) := fun t => by
    unfold hermiteStepDeriv; simp only [cl, g]
    split_ifs with h1 h2
    · rw [min_eq_right (by linarith), max_eq_left h1]; norm_num
    · rw [min_eq_left h2, max_eq_right zero_le_one]; norm_num
    · push Not at h1 h2; rw [min_eq_right h2.le, max_eq_right h1.le]
  have hcl_lip : |cl x - cl y| ≤ |x - y| := by
    have hmin : |min 1 x - min 1 y| ≤ |x - y| := by
      rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
      · rw [min_eq_right hx, min_eq_right hy]
      · rw [min_eq_right hx, min_eq_left hy, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [min_eq_left hx, min_eq_right hy, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [min_eq_left hx, min_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _
    have hmax : ∀ a b : ℝ, |max 0 a - max 0 b| ≤ |a - b| := fun a b => by
      rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
      · rw [max_eq_right ha, max_eq_right hb]
      · rw [max_eq_right ha, max_eq_left hb, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [max_eq_left ha, max_eq_right hb, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [max_eq_left ha, max_eq_left hb, sub_self, abs_zero]; exact abs_nonneg _
    exact (hmax (min 1 x) (min 1 y)).trans hmin
  rw [hcl_eq, hcl_eq]
  have h01 : ∀ t, 0 ≤ cl t ∧ cl t ≤ 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  exact (hg_lip (cl x) (cl y) (h01 x).1 (h01 x).2 (h01 y).1 (h01 y).2).trans
    (mul_le_mul_of_nonneg_left hcl_lip (by norm_num))

/-- Even `C^2` cutoff `χ_γ(u)` equal to `1` on `[-(1 - γ), 1 - γ]` and `0` outside `[-(1 - γ/2), 1 - γ/2]`. -/
noncomputable def chi (γ u : ℝ) : ℝ :=
  hermiteStep ((u ^ 2 - (1 - γ) ^ 2) / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2))

noncomputable def chiDeriv (γ u : ℝ) : ℝ :=
  hermiteStepDeriv ((u ^ 2 - (1 - γ) ^ 2) / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2)) *
    (2 * u / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2))

lemma chi_denom_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    γ / 2 ≤ (1 - γ / 2) ^ 2 - (1 - γ) ^ 2 := by
  nlinarith [hγ0, hγ1]

lemma chi_even (γ u : ℝ) : chi γ (-u) = chi γ u := by simp [chi]
lemma chi_bounds (γ u : ℝ) : 0 ≤ chi γ u ∧ chi γ u ≤ 1 := hermiteStep_bounds _

lemma chi_eq_one {γ u : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hu : |u| ≤ 1 - γ) :
    chi γ u = 1 := by
  have hd : 0 < (1 - γ / 2) ^ 2 - (1 - γ) ^ 2 := lt_of_lt_of_le (by linarith) (chi_denom_pos hγ0 hγ1)
  have hnum : u ^ 2 - (1 - γ) ^ 2 ≤ 0 := by
    have : u ^ 2 ≤ (1 - γ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg u) hu 2
    linarith
  have hle : (u ^ 2 - (1 - γ) ^ 2) / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum hd.le
  simp [chi, hermiteStep, hle]

lemma chi_eq_zero {γ u : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hu : 1 - γ / 2 ≤ |u|) :
    chi γ u = 0 := by
  have hd : 0 < (1 - γ / 2) ^ 2 - (1 - γ) ^ 2 := lt_of_lt_of_le (by linarith) (chi_denom_pos hγ0 hγ1)
  have hge : 1 ≤ (u ^ 2 - (1 - γ) ^ 2) / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2) := by
    rw [one_le_div hd]
    have hnn : 0 ≤ 1 - γ / 2 := by linarith
    have : (1 - γ / 2) ^ 2 ≤ u ^ 2 := by
      have h1 := pow_le_pow_left₀ hnn hu 2
      rwa [sq_abs] at h1
    linarith
  have hnot : ¬ (u ^ 2 - (1 - γ) ^ 2) / ((1 - γ / 2) ^ 2 - (1 - γ) ^ 2) ≤ 0 := by linarith
  simp [chi, hermiteStep, hnot, hge]

lemma hasDerivAt_chi {γ : ℝ} (_hγ0 : 0 < γ) (_hγ1 : γ ≤ 1 / 2) (u : ℝ) :
    HasDerivAt (chi γ) (chiDeriv γ u) u := by
  set d := (1 - γ / 2) ^ 2 - (1 - γ) ^ 2
  have hinner : HasDerivAt (fun t => (t ^ 2 - (1 - γ) ^ 2) / d) (2 * u / d) u :=
    ((((hasDerivAt_id u).pow 2).sub_const ((1 - γ) ^ 2)).div_const d).congr_deriv (by simp only [id_eq]; ring)
  exact (hasDerivAt_hermiteStep _).comp u hinner

lemma abs_chiDeriv_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (u : ℝ) :
    |chiDeriv γ u| ≤ 8 / γ := by
  set d := (1 - γ / 2) ^ 2 - (1 - γ) ^ 2
  have hd_def : d = (1 - γ / 2) ^ 2 - (1 - γ) ^ 2 := rfl
  have hd : γ / 2 ≤ d := chi_denom_pos hγ0 hγ1
  have hd_pos : 0 < d := by linarith
  have hcd_eq : chiDeriv γ u = hermiteStepDeriv ((u ^ 2 - (1 - γ) ^ 2) / d) * (2 * u / d) := rfl
  rw [hcd_eq]
  by_cases hu : |u| ≤ 1
  · rw [abs_mul, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_of_pos hd_pos]
    have h1 := abs_hermiteStepDeriv_le ((u ^ 2 - (1 - γ) ^ 2) / d)
    have h2 : 2 * |u| / d ≤ 4 / γ := by
      rw [div_le_div_iff₀ hd_pos hγ0]; nlinarith [hd, hu, hγ0]
    calc |hermiteStepDeriv ((u ^ 2 - (1 - γ) ^ 2) / d)| * (2 * |u| / d)
        ≤ 2 * (4 / γ) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 8 / γ := by ring
  · have hge : 1 ≤ (u ^ 2 - (1 - γ) ^ 2) / d := by
      rw [one_le_div hd_pos]
      have h1 : 1 < |u| := not_le.mp hu
      have h2 : 1 < u ^ 2 := by rw [← sq_abs]; nlinarith [h1]
      have h3 : (1 - γ / 2) ^ 2 ≤ 1 := by nlinarith [hγ0, hγ1]
      linarith [h2, h3, hd_def]
    have hnot : ¬ (u ^ 2 - (1 - γ) ^ 2) / d ≤ 0 := by linarith
    simp only [hermiteStepDeriv, if_neg hnot, if_pos hge, zero_mul, abs_zero]
    positivity

lemma chiDeriv_lip {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (x y : ℝ) :
    |chiDeriv γ x - chiDeriv γ y| ≤ (200 / γ ^ 2) * |x - y| := by
  set d := (1 - γ / 2) ^ 2 - (1 - γ) ^ 2
  have hd_def : d = (1 - γ / 2) ^ 2 - (1 - γ) ^ 2 := rfl
  have hd : γ / 2 ≤ d := chi_denom_pos hγ0 hγ1
  have hd_pos : 0 < d := by linarith
  have hzero : ∀ t, 1 ≤ |t| → hermiteStepDeriv ((t ^ 2 - (1 - γ) ^ 2) / d) = 0 := fun t ht => by
    have hge : 1 ≤ (t ^ 2 - (1 - γ) ^ 2) / d := by
      rw [one_le_div hd_pos]
      have h2 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith [ht]
      have h3 : (1 - γ / 2) ^ 2 ≤ 1 := by nlinarith [hγ0, hγ1]
      linarith [h2, h3, hd_def]
    have hnot : ¬ (t ^ 2 - (1 - γ) ^ 2) / d ≤ 0 := by linarith
    simp [hermiteStepDeriv, hnot, hge]
  have hpt : ∀ a b, |a| ≤ 1 → |b| ≤ 1 → |chiDeriv γ a - chiDeriv γ b| ≤ (200 / γ ^ 2) * |a - b| := by
    intro a b ha hb
    let s : ℝ → ℝ := fun t => (t ^ 2 - (1 - γ) ^ 2) / d
    have hdecomp : chiDeriv γ a - chiDeriv γ b =
        (hermiteStepDeriv (s a) - hermiteStepDeriv (s b)) * (2 * a / d) +
        hermiteStepDeriv (s b) * (2 * (a - b) / d) := by
      simp only [chiDeriv, s, d]; ring
    rw [hdecomp]
    have h1 : |s a - s b| ≤ (2 / d) * |a - b| := by
      have heq : s a - s b = (a + b) * (a - b) / d := by simp only [s]; ring
      rw [heq, abs_div, abs_mul, abs_of_pos hd_pos]
      have hab : |a + b| ≤ 2 := by
        have := abs_add_le a b; linarith
      calc |a + b| * |a - b| / d ≤ 2 * |a - b| / d :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab (abs_nonneg _)) hd_pos.le
        _ = (2 / d) * |a - b| := by ring
    have ht1 : |(hermiteStepDeriv (s a) - hermiteStepDeriv (s b)) * (2 * a / d)| ≤
        (40 / d ^ 2) * |a - b| := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_of_pos hd_pos]
      have hl := (hermiteStepDeriv_lip (s a) (s b)).trans (mul_le_mul_of_nonneg_left h1 (by norm_num))
      have ha2 : 2 * |a| / d ≤ 2 / d := div_le_div_of_nonneg_right (by linarith) hd_pos.le
      calc |hermiteStepDeriv (s a) - hermiteStepDeriv (s b)| * (2 * |a| / d)
          ≤ (10 * ((2 / d) * |a - b|)) * (2 / d) := mul_le_mul hl ha2 (by positivity) (by positivity)
        _ = (40 / d ^ 2) * |a - b| := by ring
    have ht2 : |hermiteStepDeriv (s b) * (2 * (a - b) / d)| ≤ (4 / d) * |a - b| := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_of_pos hd_pos]
      calc |hermiteStepDeriv (s b)| * (2 * |a - b| / d)
          ≤ 2 * (2 * |a - b| / d) := mul_le_mul_of_nonneg_right (abs_hermiteStepDeriv_le _) (by positivity)
        _ = (4 / d) * |a - b| := by ring
    have h40 : 40 / d ^ 2 + 4 / d ≤ 200 / γ ^ 2 := by
      have hd_sq : γ ^ 2 / 4 ≤ d ^ 2 := by nlinarith [hd, hγ0]
      have hA : 40 / d ^ 2 ≤ 160 / γ ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hd_pos) (sq_pos_of_pos hγ0)]; nlinarith [hd_sq]
      have hB : 4 / d ≤ 8 / γ := by
        rw [div_le_div_iff₀ hd_pos hγ0]; nlinarith [hd]
      have hC : 8 / γ ≤ 40 / γ ^ 2 := by
        rw [div_le_div_iff₀ hγ0 (sq_pos_of_pos hγ0)]; nlinarith [hγ0, hγ1]
      have hsum : 160 / γ ^ 2 + 40 / γ ^ 2 = 200 / γ ^ 2 := by ring
      linarith [hA, hB, hC, hsum]
    exact (abs_add_le _ _).trans (by
      have := add_le_add ht1 ht2
      have hle : (40 / d ^ 2 + 4 / d) * |a - b| ≤ (200 / γ ^ 2) * |a - b| :=
        mul_le_mul_of_nonneg_right h40 (abs_nonneg _)
      linarith)
  let cl : ℝ → ℝ := fun t => max (-1) (min 1 t)
  have hcl_eq : ∀ t, chiDeriv γ t = chiDeriv γ (cl t) := fun t => by
    rcases le_or_gt |t| 1 with h1 | h1
    · have hcl : cl t = t := by
        simp only [cl, min_eq_right (abs_le.mp h1).2, max_eq_right (abs_le.mp h1).1]
      rw [hcl]
    · have hc1 : |cl t| = 1 := by
        rcases le_or_gt t (-1) with hl | hl
        · simp [cl, min_eq_right (by linarith : t ≤ 1), max_eq_left hl]
        · have hr : 1 ≤ t := by
            rcases le_or_gt 0 t with ht0 | ht0
            · rw [abs_of_nonneg ht0] at h1; linarith
            · rw [abs_of_neg ht0] at h1; linarith
          simp [cl, min_eq_left hr]
      have h1' : chiDeriv γ t = 0 := by
        change hermiteStepDeriv ((t ^ 2 - (1 - γ) ^ 2) / d) * (2 * t / d) = 0
        rw [hzero t h1.le, zero_mul]
      have h2' : chiDeriv γ (cl t) = 0 := by
        change hermiteStepDeriv (((cl t) ^ 2 - (1 - γ) ^ 2) / d) * (2 * cl t / d) = 0
        rw [hzero (cl t) hc1.ge, zero_mul]
      rw [h1', h2']
  have hcl_bd : ∀ t, |cl t| ≤ 1 := fun t => by
    rw [abs_le]; exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hcl_lip : |cl x - cl y| ≤ |x - y| := by
    have hmin : |min 1 x - min 1 y| ≤ |x - y| := by
      rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
      · rw [min_eq_right hx, min_eq_right hy]
      · rw [min_eq_right hx, min_eq_left hy, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [min_eq_left hx, min_eq_right hy, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [min_eq_left hx, min_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _
    have hmax : ∀ a b : ℝ, |max (-1) a - max (-1) b| ≤ |a - b| := fun a b => by
      rcases le_total (-1) a with ha | ha <;> rcases le_total (-1) b with hb | hb
      · rw [max_eq_right ha, max_eq_right hb]
      · rw [max_eq_right ha, max_eq_left hb, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [max_eq_left ha, max_eq_right hb, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [max_eq_left ha, max_eq_left hb, sub_self, abs_zero]; exact abs_nonneg _
    exact (hmax (min 1 x) (min 1 y)).trans hmin
  rw [hcl_eq x, hcl_eq y]
  exact (hpt (cl x) (cl y) (hcl_bd x) (hcl_bd y)).trans
    (mul_le_mul_of_nonneg_left hcl_lip (by positivity))

lemma chi_taylor {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (a h : ℝ) :
    |chi γ (a + h) - chi γ a - chiDeriv γ a * h| ≤ (200 / γ ^ 2) * h ^ 2 :=
  taylor_of_deriv_lip (by positivity) (hasDerivAt_chi hγ0 hγ1) (chiDeriv_lip hγ0 hγ1) a h

lemma chi_lip {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (x y : ℝ) :
    |chi γ x - chi γ y| ≤ (8 / γ) * |x - y| :=
  lip_of_deriv_bound (by positivity) (hasDerivAt_chi hγ0 hγ1) (abs_chiDeriv_le hγ0 hγ1) x y

/-- Odd `C^2` kick truncation `τ(z) = 2 z / √(4 + z^2)` bounded in `(-2, 2)`. -/
noncomputable def tau (z : ℝ) : ℝ := 2 * z / Real.sqrt (4 + z ^ 2)

lemma tau_neg (z : ℝ) : tau (-z) = -tau z := by
  simp only [tau, neg_sq]; ring

lemma abs_tau_lt_two (z : ℝ) : |tau z| < 2 := by
  simp only [tau, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2),
    abs_of_pos (Real.sqrt_pos.mpr (by positivity : 0 < 4 + z ^ 2))]
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  have h1 : |z| < Real.sqrt (4 + z ^ 2) := by
    have hsq : |z| ^ 2 < (Real.sqrt (4 + z ^ 2)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt (by positivity)]; linarith
    nlinarith [hsq, abs_nonneg z, Real.sqrt_nonneg (4 + z ^ 2)]
  linarith

lemma hasDerivAt_tau (z : ℝ) :
    HasDerivAt tau (8 / (4 + z ^ 2) / Real.sqrt (4 + z ^ 2)) z := by
  have hs : HasDerivAt (fun t => Real.sqrt (4 + t ^ 2)) (z / Real.sqrt (4 + z ^ 2)) z := by
    have h0 : HasDerivAt (fun t => 4 + t ^ 2) (2 * z) z :=
      ((hasDerivAt_const z (4 : ℝ)).add ((hasDerivAt_id z).pow 2)).congr_deriv (by simp only [id_eq]; ring)
    exact (h0.sqrt (by positivity : 4 + z ^ 2 ≠ 0)).congr_deriv (by
      have hne : Real.sqrt (4 + z ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp [hne])
  have hq := ((hasDerivAt_id z).const_mul 2).div hs (Real.sqrt_pos.mpr (by positivity)).ne'
  exact hq.congr_deriv (by
    simp only [id_eq]
    have hsq : Real.sqrt (4 + z ^ 2) ^ 2 = 4 + z ^ 2 := Real.sq_sqrt (by positivity)
    have hne : Real.sqrt (4 + z ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have h1 : 2 * 1 * Real.sqrt (4 + z ^ 2) - 2 * z * (z / Real.sqrt (4 + z ^ 2)) =
        8 / Real.sqrt (4 + z ^ 2) := by
      rw [eq_div_iff hne, sub_mul, mul_assoc (2 * z), div_mul_cancel₀ _ hne]
      have h2 : 2 * 1 * Real.sqrt (4 + z ^ 2) * Real.sqrt (4 + z ^ 2) = 2 * (4 + z ^ 2) := by
        rw [mul_assoc, ← sq, hsq]; ring
      linarith only [h2]
    rw [h1, hsq, div_right_comm])

lemma tau_lip (x y : ℝ) : |tau x - tau y| ≤ |x - y| := by
  have h := lip_of_deriv_bound zero_le_one hasDerivAt_tau (fun t => by
    have hpos : 0 < 8 / (4 + t ^ 2) / Real.sqrt (4 + t ^ 2) := by positivity
    rw [abs_of_pos hpos, div_le_one (Real.sqrt_pos.mpr (by positivity))]
    have h1 : 4 ≤ 4 + t ^ 2 := by linarith [sq_nonneg t]
    have h2 : 2 ≤ Real.sqrt (4 + t ^ 2) := by
      have hsq : (2 : ℝ) ^ 2 ≤ (Real.sqrt (4 + t ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]; linarith
      nlinarith [hsq, Real.sqrt_nonneg (4 + t ^ 2)]
    rw [div_le_iff₀ (by positivity)]; nlinarith [h1, h2]) x y
  simpa using h

/-- Uniform lower bound `E[τ((1/√n) ∑ ζ_j)^2] ≥ 1 / 25` for all `n ≥ 1`. -/
lemma tau_rademacher_second_moment {n : ℕ} (hn : 1 ≤ n) :
    (1 / 25 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ) ≤
      ∑ ζ : Fin n → Bool,
        (tau ((∑ j : Fin n, if ζ j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let S : (Fin n → Bool) → ℝ := fun ζ => (∑ j : Fin n, if ζ j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ)
  let r : (Fin n → Bool) → Fin n → ℝ := fun ζ j => if ζ j then 1 else -1
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 ^ n : ℝ) := by simp
  have hflip_zero : ∀ (i : Fin n) (g : (Fin n → Bool) → ℝ),
      (∀ ζ, g (Function.update ζ i (!ζ i)) = -g ζ) → ∑ ζ : Fin n → Bool, g ζ = 0 := by
    intro i g hg
    let inv : (Fin n → Bool) ≃ (Fin n → Bool) :=
      ⟨fun ζ => Function.update ζ i (!ζ i), fun ζ => Function.update ζ i (!ζ i),
       fun ζ => by funext j; by_cases h : j = i <;> simp [h],
       fun ζ => by funext j; by_cases h : j = i <;> simp [h]⟩
    have h1 : ∑ ζ : Fin n → Bool, g ζ = ∑ ζ : Fin n → Bool, -g ζ := by
      calc ∑ ζ, g ζ = ∑ ζ, g (inv ζ) := (Equiv.sum_comp inv g).symm
        _ = ∑ ζ, -g ζ := Finset.sum_congr rfl fun ζ _ => hg ζ
    rw [Finset.sum_neg_distrib] at h1
    linarith
  have hr_upd : ∀ (ζ : Fin n → Bool) (a j : Fin n),
      r (Function.update ζ a (!ζ a)) j = if j = a then -r ζ j else r ζ j := fun ζ a j => by
    by_cases h : j = a
    · subst h; simp only [r, Function.update_self, ite_true]; cases ζ j <;> norm_num
    · simp only [r, Function.update_of_ne h, if_neg h]
  have hr_pair : ∀ i j : Fin n, i ≠ j → ∑ ζ : Fin n → Bool, r ζ i * r ζ j = 0 := by
    intro i j hij
    refine hflip_zero i (fun ζ => r ζ i * r ζ j) fun ζ => ?_
    rw [hr_upd, hr_upd, if_pos rfl, if_neg hij.symm]; ring
  have hE2 : ∑ ζ : Fin n → Bool, (S ζ) ^ 2 = (Fintype.card (Fin n → Bool) : ℝ) := by
    have h1 : ∀ ζ, (S ζ) ^ 2 = (∑ i : Fin n, ∑ j : Fin n, r ζ i * r ζ j) / (n : ℝ) := fun ζ => by
      simp only [S, r]
      rw [div_pow, Real.sq_sqrt hn_pos.le, sq, Finset.sum_mul]
      congr 1; refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    simp_rw [h1]
    rw [← Finset.sum_div, Finset.sum_comm]
    have hinner : ∀ i : Fin n, ∑ ζ : Fin n → Bool, ∑ j : Fin n, r ζ i * r ζ j =
        (Fintype.card (Fin n → Bool) : ℝ) := by
      intro i
      rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hdiag : ∑ ζ : Fin n → Bool, r ζ i * r ζ i = (Fintype.card (Fin n → Bool) : ℝ) := by
        have h1 : ∀ ζ, r ζ i * r ζ i = (1 : ℝ) := fun ζ => by simp only [r]; cases ζ i <;> norm_num
        simp [h1]
      have hoff : ∑ j ∈ Finset.univ.erase i, ∑ ζ : Fin n → Bool, r ζ i * r ζ j = 0 :=
        Finset.sum_eq_zero fun j hj => hr_pair i j (Finset.ne_of_mem_erase hj).symm
      linarith [hdiag, hoff]
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hn_pos.ne']
  have hE4 : ∑ ζ : Fin n → Bool, (S ζ) ^ 4 ≤ 3 * (Fintype.card (Fin n → Bool) : ℝ) := by
    have h1 : ∀ ζ, (S ζ) ^ 4 =
        (∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄) / (n : ℝ) ^ 2 := fun ζ => by
      have hsq : (S ζ) ^ 2 = (∑ i : Fin n, r ζ i) ^ 2 / (n : ℝ) := by
        simp only [S, r, div_pow, Real.sq_sqrt hn_pos.le]
      have h2 : (∑ i : Fin n, r ζ i) ^ 2 = ∑ i₁ : Fin n, ∑ i₂ : Fin n, r ζ i₁ * r ζ i₂ := by
        rw [sq, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      rw [show (S ζ) ^ 4 = ((S ζ) ^ 2) ^ 2 by ring, hsq, div_pow, h2]
      congr 1
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₁ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i₃ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i₄ _ => by ring
    simp_rw [h1]
    rw [← Finset.sum_div, div_le_iff₀ (sq_pos_of_pos hn_pos)]
    have hquad_sum : ∑ ζ : Fin n → Bool,
        ∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ =
        ∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Bool)))]
    rw [hquad_sum]
    have hzero_odd : ∀ i₁ i₂ i₃ i₄ : Fin n,
        (¬ ((i₁ = i₂ ∧ i₃ = i₄) ∨ (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃))) →
        ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ = 0 := by
      intro i₁ i₂ i₃ i₄ hnot
      have hodd : ∀ a : Fin n,
          (a = i₁ ∧ a ≠ i₂ ∧ a ≠ i₃ ∧ a ≠ i₄) ∨
          (a = i₂ ∧ a ≠ i₁ ∧ a ≠ i₃ ∧ a ≠ i₄) ∨
          (a = i₃ ∧ a ≠ i₁ ∧ a ≠ i₂ ∧ a ≠ i₄) ∨
          (a = i₄ ∧ a ≠ i₁ ∧ a ≠ i₂ ∧ a ≠ i₃) →
          ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ = 0 := by
        intro a hcase
        refine hflip_zero a (fun ζ => r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄) fun ζ => ?_
        rcases hcase with ⟨rfl, h2, h3, h4⟩ | ⟨rfl, h1, h3, h4⟩ | ⟨rfl, h1, h2, h4⟩ | ⟨rfl, h1, h2, h3⟩
        · rw [hr_upd, hr_upd, hr_upd, hr_upd, if_pos rfl, if_neg h2.symm, if_neg h3.symm, if_neg h4.symm]; ring
        · rw [hr_upd, hr_upd, hr_upd, hr_upd, if_neg h1.symm, if_pos rfl, if_neg h3.symm, if_neg h4.symm]; ring
        · rw [hr_upd, hr_upd, hr_upd, hr_upd, if_neg h1.symm, if_neg h2.symm, if_pos rfl, if_neg h4.symm]; ring
        · rw [hr_upd, hr_upd, hr_upd, hr_upd, if_neg h1.symm, if_neg h2.symm, if_neg h3.symm, if_pos rfl]; ring
      by_cases h12 : i₁ = i₂
      · have h34 : i₃ ≠ i₄ := fun h => hnot (Or.inl ⟨h12, h⟩)
        by_cases h13 : i₁ = i₃
        · exact hodd i₄ (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [h13]; exact h34.symm,
            by rw [← h12, h13]; exact h34.symm, h34.symm⟩)))
        · exact hodd i₃ (Or.inr (Or.inr (Or.inl ⟨rfl, Ne.symm h13,
            by rw [← h12]; exact Ne.symm h13, h34⟩)))
      · by_cases h13 : i₁ = i₃
        · have h24 : i₂ ≠ i₄ := fun h => hnot (Or.inr (Or.inl ⟨h13, h⟩))
          exact hodd i₂ (Or.inr (Or.inl ⟨rfl, Ne.symm h12,
            by rw [← h13]; exact Ne.symm h12, h24⟩))
        · by_cases h14 : i₁ = i₄
          · have h23 : i₂ ≠ i₃ := fun h => hnot (Or.inr (Or.inr ⟨h14, h⟩))
            exact hodd i₂ (Or.inr (Or.inl ⟨rfl, Ne.symm h12, h23,
              by rw [← h14]; exact Ne.symm h12⟩))
          · exact hodd i₁ (Or.inl ⟨rfl, h12, h13, h14⟩)
    have hterm_le : ∀ i₁ i₂ i₃ i₄ : Fin n,
        ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ ≤
        ((if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0)) * (Fintype.card (Fin n → Bool) : ℝ) := by
      intro i₁ i₂ i₃ i₄
      by_cases hp : (i₁ = i₂ ∧ i₃ = i₄) ∨ (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃)
      · have hle1 : ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄ ≤
            (Fintype.card (Fin n → Bool) : ℝ) := by
          calc _ ≤ ∑ _ζ : Fin n → Bool, (1 : ℝ) := Finset.sum_le_sum fun ζ _ => by
                simp only [r]; cases ζ i₁ <;> cases ζ i₂ <;> cases ζ i₃ <;> cases ζ i₄ <;> norm_num
            _ = (Fintype.card (Fin n → Bool) : ℝ) := by simp
        have hge1 : (1 : ℝ) ≤ (if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
            (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
            (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) := by
          rcases hp with h | h | h <;> simp [h] <;> split_ifs <;> linarith
        exact hle1.trans (by nlinarith [hge1, Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin n → Bool))])
      · rw [hzero_odd i₁ i₂ i₃ i₄ hp]
        positivity
    have hsum_ind : ∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
        ((if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0)) = 3 * (n : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, ite_and]
      have hA : (∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          if i₁ = i₂ then if i₃ = i₄ then (1 : ℝ) else 0 else 0) = (n : ℝ) ^ 2 := by
        simp [sq]
      have hB : (∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          if i₁ = i₃ then if i₂ = i₄ then (1 : ℝ) else 0 else 0) = (n : ℝ) ^ 2 := by
        simp [sq]
      have hC : (∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          if i₁ = i₄ then if i₂ = i₃ then (1 : ℝ) else 0 else 0) = (n : ℝ) ^ 2 := by
        simp [sq]
      linarith [hA, hB, hC]
    calc ∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
          ∑ ζ : Fin n → Bool, r ζ i₁ * r ζ i₂ * r ζ i₃ * r ζ i₄
        ≤ ∑ i₁ : Fin n, ∑ i₂ : Fin n, ∑ i₃ : Fin n, ∑ i₄ : Fin n,
            ((if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
             (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
             (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0)) * (Fintype.card (Fin n → Bool) : ℝ) :=
          Finset.sum_le_sum fun i₁ _ => Finset.sum_le_sum fun i₂ _ =>
            Finset.sum_le_sum fun i₃ _ => Finset.sum_le_sum fun i₄ _ => hterm_le i₁ i₂ i₃ i₄
      _ = (3 * (n : ℝ) ^ 2) * (Fintype.card (Fin n → Bool) : ℝ) := by
          simp_rw [← Finset.sum_mul, hsum_ind]
      _ = 3 * (Fintype.card (Fin n → Bool) : ℝ) * (n : ℝ) ^ 2 := by ring
  -- Paley–Zygmund on `S^2`: `Pr[S^2 ≥ 1/4] ≥ 3/16`, and on `S^2 ≥ 1/4`, `tau(S)^2 ≥ 4/17`.
  let Good := Finset.univ.filter (fun ζ : Fin n → Bool => (1 / 4 : ℝ) ≤ (S ζ) ^ 2)
  have hPZ : (3 / 16 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ) ≤ (Good.card : ℝ) := by
    have hsplit : (Fintype.card (Fin n → Bool) : ℝ) ≤
        (1 / 4) * (Fintype.card (Fin n → Bool) : ℝ) + ∑ ζ ∈ Good, (S ζ) ^ 2 := by
      rw [← hE2]
      have hcov : ∑ ζ : Fin n → Bool, (S ζ) ^ 2 =
          (∑ ζ ∈ Good, (S ζ) ^ 2) + ∑ ζ ∈ Finset.univ \ Good, (S ζ) ^ 2 :=
        (Finset.sum_add_sum_compl Good (fun ζ => (S ζ) ^ 2)).symm
      have hbad : ∑ ζ ∈ Finset.univ \ Good, (S ζ) ^ 2 ≤ (1 / 4) * (Fintype.card (Fin n → Bool) : ℝ) := by
        calc ∑ ζ ∈ Finset.univ \ Good, (S ζ) ^ 2
            ≤ ∑ _ζ ∈ Finset.univ \ Good, (1 / 4 : ℝ) := Finset.sum_le_sum fun ζ hζ => by
              have hnot : ¬ (1 / 4 : ℝ) ≤ (S ζ) ^ 2 := by
                intro h; exact (Finset.mem_sdiff.mp hζ).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
              linarith
          _ = ((Finset.univ \ Good).card : ℝ) * (1 / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Fintype.card (Fin n → Bool) : ℝ) * (1 / 4) := by
              refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
              exact_mod_cast Finset.card_le_univ (Finset.univ \ Good)
          _ = (1 / 4) * (Fintype.card (Fin n → Bool) : ℝ) := mul_comm _ _
      linarith [hcov, hbad]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Good (fun _ => (1 : ℝ)) (fun ζ => (S ζ) ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have h4sub : ∑ ζ ∈ Good, ((S ζ) ^ 2) ^ 2 ≤ 3 * (Fintype.card (Fin n → Bool) : ℝ) := by
      have hrew : ∀ ζ, ((S ζ) ^ 2) ^ 2 = (S ζ) ^ 4 := fun ζ => by ring
      simp_rw [hrew]
      exact (Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity).trans hE4
    have hsq_ge : ((3 / 4 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ)) ^ 2 ≤
        (Good.card : ℝ) * (3 * (Fintype.card (Fin n → Bool) : ℝ)) := by
      have h34 : (3 / 4 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ) ≤ ∑ ζ ∈ Good, (S ζ) ^ 2 := by
        linarith [hsplit]
      have hsq1 := pow_le_pow_left₀ (by positivity) h34 2
      exact hsq1.trans (hcs.trans (mul_le_mul_of_nonneg_left h4sub (Nat.cast_nonneg _)))
    have hFpos : (0 : ℝ) < (Fintype.card (Fin n → Bool) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    nlinarith [hsq_ge, hFpos]
  have htau_good : ∀ ζ ∈ Good, (4 / 17 : ℝ) ≤ (tau (S ζ)) ^ 2 := fun ζ hζ => by
    have hge : (1 / 4 : ℝ) ≤ (S ζ) ^ 2 := (Finset.mem_filter.mp hζ).2
    simp only [tau, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 + (S ζ) ^ 2)]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  calc (1 / 25 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ)
      ≤ (4 / 17 : ℝ) * ((3 / 16 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ)) := by
        have : (0 : ℝ) ≤ (Fintype.card (Fin n → Bool) : ℝ) := Nat.cast_nonneg _
        linarith
    _ ≤ (4 / 17 : ℝ) * (Good.card : ℝ) := mul_le_mul_of_nonneg_left hPZ (by norm_num)
    _ = ∑ _ζ ∈ Good, (4 / 17 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ ζ ∈ Good, (tau (S ζ)) ^ 2 := Finset.sum_le_sum htau_good
    _ ≤ ∑ ζ : Fin n → Bool, (tau (S ζ)) ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _

end SmoothProx


/- ### Section 5: Kicked Proximal Ascent Dynamics, Antisymmetry, and Efron–Stein Concentration -/

section KickedProx

/-- Independent Rademacher kick bits: `n` bits per vertex per step so each bit has `O(1/√n)` sensitivity. -/
abbrev KickBits (T n : ℕ) : Type := Fin T → Fin n → Fin n → Bool

/-- Antisymmetric initial vector `x_0 ∈ {-1/2, 0, +1/2}^n`. -/
noncomputable def iterInit (n : ℕ) (v : Fin n) : ℝ :=
  if v.val < n / 2 then 1 / 2 else if v.val < 2 * (n / 2) then -1 / 2 else 0

/-- Bounded `C^2` kick value `W(ζ, s, v) = τ((1/√n) ∑_j ±1) ∈ (-2, 2)`. -/
noncomputable def kickVal {T n : ℕ} (ζ : KickBits T n) (s : ℕ) (v : Fin n) : ℝ :=
  if h : s < T then
    tau ((∑ j : Fin n, if ζ ⟨s, h⟩ v j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))
  else 0

/-- Kick map `x̃_s(v) = x_s(v) + σ χ_γ(x_s(v)) W(ζ, s, v)`. -/
noncomputable def iterKick {T n : ℕ} (γ σ : ℝ) (ζ : KickBits T n) (s : ℕ) (x : Fin n → ℝ)
    (v : Fin n) : ℝ :=
  x v + σ * chi γ (x v) * kickVal ζ s v

/-- Scaled graph gradient `(1 / √n) A(ω) x`. -/
noncomputable def iterGrad {n : ℕ} (ω : EdgeIdx n → Bool) (x : Fin n → ℝ) (v : Fin n) : ℝ :=
  (∑ w : Fin n, adjSign ω v w * x w) / Real.sqrt (n : ℝ)

/-- One step of kicked `C^2` proximal gradient ascent with step size `η = 1 / 20`. -/
noncomputable def iterStep {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (s : ℕ) (x : Fin n → ℝ) (v : Fin n) : ℝ :=
  let xt := iterKick γ σ ζ s x
  psi lam (xt v + (1 / 20 : ℝ) * iterGrad ω xt v)

/-- Trajectory `x_0, x_1, ..., x_T` of kicked proximal gradient ascent. -/
noncomputable def iterState {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n) :
    ℕ → Fin n → ℝ
  | 0 => iterInit n
  | s + 1 => iterStep lam γ σ ω ζ s (iterState lam γ σ ω ζ s)

lemma abs_kickVal_lt_two {T n : ℕ} (ζ : KickBits T n) (s : ℕ) (v : Fin n) :
    |kickVal ζ s v| < 2 := by
  unfold kickVal
  split_ifs
  · exact abs_tau_lt_two _
  · norm_num

lemma abs_iterInit_le_half (n : ℕ) (v : Fin n) : |iterInit n v| ≤ 1 / 2 := by
  unfold iterInit; split_ifs <;> norm_num

lemma abs_iterState_lt_one {T n : ℕ} {lam γ σ : ℝ} (hlam : 0 < lam)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n) (t : ℕ) (v : Fin n) :
    |iterState lam γ σ ω ζ t v| < 1 := by
  cases t with
  | zero => exact lt_of_le_of_lt (abs_iterInit_le_half n v) (by norm_num)
  | succ s => exact abs_psi_lt_one hlam _

lemma iterKick_eq_self_of_outer {T n : ℕ} {γ σ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ζ : KickBits T n) (s : ℕ) (x : Fin n → ℝ) (v : Fin n) (hv : 1 - γ / 2 ≤ |x v|) :
    iterKick γ σ ζ s x v = x v := by
  simp [iterKick, chi_eq_zero hγ0 hγ1 hv]

lemma abs_iterKick_interior {T n : ℕ} {γ σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ζ : KickBits T n) (s : ℕ) (x : Fin n → ℝ) (v : Fin n) (hv : |x v| ≤ 1 - γ / 2) :
    |iterKick γ σ ζ s x v| ≤ 1 - γ / 4 := by
  unfold iterKick
  have hchi := chi_bounds γ (x v)
  have hW := abs_kickVal_lt_two ζ s v
  have hkick : |σ * chi γ (x v) * kickVal ζ s v| ≤ γ / 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg hchi.1]
    calc σ * chi γ (x v) * |kickVal ζ s v|
        ≤ (γ / 8) * 1 * 2 :=
          mul_le_mul (mul_le_mul hσ hchi.2 hchi.1 (by linarith)) hW.le (abs_nonneg _) (by linarith)
      _ = γ / 4 := by ring
  exact (abs_add_le _ _).trans (by linarith)

lemma abs_iterKick_lt_one {T n : ℕ} {γ σ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ζ : KickBits T n) (s : ℕ) (x : Fin n → ℝ) (v : Fin n) (hv : |x v| < 1) :
    |iterKick γ σ ζ s x v| < 1 := by
  rcases le_or_gt (1 - γ / 2) |x v| with hout | hin
  · rw [iterKick_eq_self_of_outer hγ0 hγ1 ζ s x v hout]; exact hv
  · exact lt_of_le_of_lt (abs_iterKick_interior hσ0 hσ ζ s x v hin.le) (by linarith)

/- #### Exact Involution Antisymmetry (`E[mean(x_t)] = 0`) -/

/-- Involution on `Fin n` swapping `[0, n/2)` with `[n/2, 2*(n/2))` and fixing `2*(n/2)` if `n` is odd. -/
def swapPerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i :=
    if h1 : i.val < n / 2 then ⟨i.val + n / 2, by omega⟩
    else if h2 : i.val < 2 * (n / 2) then ⟨i.val - n / 2, by omega⟩
    else i
  invFun i :=
    if h1 : i.val < n / 2 then ⟨i.val + n / 2, by omega⟩
    else if h2 : i.val < 2 * (n / 2) then ⟨i.val - n / 2, by omega⟩
    else i
  left_inv i := by
    ext
    by_cases h1 : i.val < n / 2
    · have hnot : ¬ (i.val + n / 2 < n / 2) := by omega
      have hlt2 : i.val + n / 2 < 2 * (n / 2) := by omega
      simp [h1, hnot, hlt2]
    · by_cases h2 : i.val < 2 * (n / 2)
      · have hlt1 : i.val - n / 2 < n / 2 := by omega
        simp [h1, h2, hlt1]; omega
      · simp [h1, h2]
  right_inv i := by
    ext
    by_cases h1 : i.val < n / 2
    · have hnot : ¬ (i.val + n / 2 < n / 2) := by omega
      have hlt2 : i.val + n / 2 < 2 * (n / 2) := by omega
      simp [h1, hnot, hlt2]
    · by_cases h2 : i.val < 2 * (n / 2)
      · have hlt1 : i.val - n / 2 < n / 2 := by omega
        simp [h1, h2, hlt1]; omega
      · simp [h1, h2]

lemma swapPerm_involutive (n : ℕ) (i : Fin n) : swapPerm n (swapPerm n i) = i :=
  (swapPerm n).left_inv i

lemma iterInit_swap (n : ℕ) (v : Fin n) : iterInit n (swapPerm n v) = -iterInit n v := by
  unfold iterInit swapPerm
  dsimp only [Equiv.coe_fn_mk]
  by_cases h1 : v.val < n / 2
  · have hnot : ¬ (v.val + n / 2 < n / 2) := by omega
    have h2 : v.val + n / 2 < 2 * (n / 2) := by omega
    simp [h1, hnot, h2]; ring
  · by_cases h2 : v.val < 2 * (n / 2)
    · have hlt : v.val - n / 2 < n / 2 := by omega
      simp [h1, h2, hlt]; ring
    · simp [h1, h2]

/-- Action of a vertex permutation on Boolean edge assignments `EdgeIdx n → Bool`. -/
def permEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (ω : EdgeIdx n → Bool) : EdgeIdx n → Bool :=
  fun e =>
    if h : π e.1.1 < π e.1.2 then ω ⟨(π e.1.1, π e.1.2), h⟩
    else ω ⟨(π e.1.2, π e.1.1), lt_of_le_of_ne (not_lt.mp h) (fun hEq => e.2.ne (π.injective hEq.symm))⟩

lemma adjSign_permEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (ω : EdgeIdx n → Bool) (u v : Fin n) :
    adjSign (permEdge π ω) u v = adjSign ω (π u) (π v) := by
  unfold adjSign permEdge
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · simp only [dif_pos hlt]
    rcases lt_or_gt_of_ne (π.injective.ne hlt.ne) with h1 | h2
    · simp only [dif_pos h1]
    · have h2' : ¬ π u < π v := lt_asymm h2
      simp only [dif_neg h2', dif_pos h2]
  · simp
  · have hnot : ¬ u < v := lt_asymm hgt
    simp only [dif_neg hnot, dif_pos hgt]
    rcases lt_or_gt_of_ne (π.injective.ne hgt.ne) with h1 | h2
    · have h1' : ¬ π u < π v := lt_asymm h1
      simp only [dif_pos h1, dif_neg h1']
    · have h2' : ¬ π v < π u := lt_asymm h2
      simp only [dif_neg h2', dif_pos h2]

lemma permEdge_swap_involutive {n : ℕ} (ω : EdgeIdx n → Bool) :
    permEdge (swapPerm n) (permEdge (swapPerm n) ω) = ω := by
  funext e
  rcases e with ⟨⟨u, v⟩, huv⟩
  have h1 : adjSign (permEdge (swapPerm n) (permEdge (swapPerm n) ω)) u v = adjSign ω u v := by
    rw [adjSign_permEdge, adjSign_permEdge, swapPerm_involutive, swapPerm_involutive]
  unfold adjSign at h1
  simp only [dif_pos huv] at h1
  cases ha : permEdge (swapPerm n) (permEdge (swapPerm n) ω) ⟨(u, v), huv⟩ <;>
    cases hb : ω ⟨(u, v), huv⟩ <;> simp_all <;> linarith

/-- Joint vertex-swap and sign-flip involution on kick bits. -/
def flipKick {T n : ℕ} (π : Equiv.Perm (Fin n)) (ζ : KickBits T n) : KickBits T n :=
  fun s v j => !(ζ s (π v) j)

lemma flipKick_swap_involutive {T n : ℕ} (ζ : KickBits T n) :
    flipKick (swapPerm n) (flipKick (swapPerm n) ζ) = ζ := by
  funext s v j
  simp [flipKick, swapPerm_involutive]

lemma kickVal_flipKick {T n : ℕ} (π : Equiv.Perm (Fin n)) (ζ : KickBits T n) (s : ℕ) (v : Fin n) :
    kickVal (flipKick π ζ) s v = -kickVal ζ s (π v) := by
  unfold kickVal flipKick
  split_ifs with h
  · have hsum : (∑ j : Fin n, if !(ζ ⟨s, h⟩ (π v) j) then (1 : ℝ) else -1) =
        -(∑ j : Fin n, if ζ ⟨s, h⟩ (π v) j then (1 : ℝ) else -1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => by cases ζ ⟨s, h⟩ (π v) j <;> norm_num
    rw [hsum, neg_div, tau_neg]
  · ring

lemma iterState_antisymm {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n) :
    ∀ (t : ℕ) (v : Fin n),
      iterState lam γ σ (permEdge (swapPerm n) ω) (flipKick (swapPerm n) ζ) t v =
        -iterState lam γ σ ω ζ t (swapPerm n v)
  | 0, v => by simp [iterState, iterInit_swap]
  | s + 1, v => by
    have ih := iterState_antisymm lam γ σ ω ζ s
    let π := swapPerm n
    let x := iterState lam γ σ ω ζ s
    let x' := iterState lam γ σ (permEdge π ω) (flipKick π ζ) s
    have hxt : ∀ w : Fin n, iterKick γ σ (flipKick π ζ) s x' w = -iterKick γ σ ζ s x (π w) := by
      intro w
      simp only [iterKick, x', x, π, ih w, chi_even, kickVal_flipKick]
      ring
    have hgrad : iterGrad (permEdge π ω) (iterKick γ σ (flipKick π ζ) s x') v =
        -iterGrad ω (iterKick γ σ ζ s x) (π v) := by
      simp only [iterGrad]
      have hnum : (∑ w : Fin n, adjSign (permEdge π ω) v w * iterKick γ σ (flipKick π ζ) s x' w) =
          -(∑ u : Fin n, adjSign ω (π v) u * iterKick γ σ ζ s x u) := by
        calc ∑ w : Fin n, adjSign (permEdge π ω) v w * iterKick γ σ (flipKick π ζ) s x' w
            = ∑ w : Fin n, -(adjSign ω (π v) (π w) * iterKick γ σ ζ s x (π w)) := by
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [adjSign_permEdge, hxt w]; ring
          _ = -(∑ w : Fin n, adjSign ω (π v) (π w) * iterKick γ σ ζ s x (π w)) := by
              rw [Finset.sum_neg_distrib]
          _ = -(∑ u : Fin n, adjSign ω (π v) u * iterKick γ σ ζ s x u) := by
              congr 1; exact Equiv.sum_comp π (fun u => adjSign ω (π v) u * iterKick γ σ ζ s x u)
      rw [hnum, neg_div]
    change psi lam (iterKick γ σ (flipKick π ζ) s x' v +
        (1 / 20 : ℝ) * iterGrad (permEdge π ω) (iterKick γ σ (flipKick π ζ) s x') v) =
      -psi lam (iterKick γ σ ζ s x (π v) + (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s x) (π v))
    rw [hxt v, hgrad, show -iterKick γ σ ζ s x (π v) +
        (1 / 20 : ℝ) * -iterGrad ω (iterKick γ σ ζ s x) (π v) =
        -(iterKick γ σ ζ s x (π v) + (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s x) (π v)) by ring,
      psi_neg]

/-- Exact zero expectation of `(1 / n) ∑_v x_t(v)` over uniform `(ω, ζ)`. -/
lemma avg_mean_iterState_eq_zero {T n : ℕ} (lam γ σ : ℝ) (t : ℕ) :
    ∑ p : (EdgeIdx n → Bool) × KickBits T n,
      (∑ v : Fin n, iterState lam γ σ p.1 p.2 t v) / (n : ℝ) = 0 := by
  let inv : ((EdgeIdx n → Bool) × KickBits T n) ≃ ((EdgeIdx n → Bool) × KickBits T n) :=
    ⟨fun p => (permEdge (swapPerm n) p.1, flipKick (swapPerm n) p.2),
     fun p => (permEdge (swapPerm n) p.1, flipKick (swapPerm n) p.2),
     fun ⟨ω, ζ⟩ => Prod.ext (permEdge_swap_involutive ω) (flipKick_swap_involutive ζ),
     fun ⟨ω, ζ⟩ => Prod.ext (permEdge_swap_involutive ω) (flipKick_swap_involutive ζ)⟩
  have hneg : ∀ p : (EdgeIdx n → Bool) × KickBits T n,
      (∑ v : Fin n, iterState lam γ σ (inv p).1 (inv p).2 t v) / (n : ℝ) =
        -((∑ v : Fin n, iterState lam γ σ p.1 p.2 t v) / (n : ℝ)) := by
    intro ⟨ω, ζ⟩
    have hsum : (∑ v : Fin n, iterState lam γ σ (permEdge (swapPerm n) ω) (flipKick (swapPerm n) ζ) t v) =
        -(∑ v : Fin n, iterState lam γ σ ω ζ t v) := by
      calc _ = ∑ v : Fin n, -iterState lam γ σ ω ζ t (swapPerm n v) :=
            Finset.sum_congr rfl fun v _ => iterState_antisymm lam γ σ ω ζ t v
        _ = -(∑ v : Fin n, iterState lam γ σ ω ζ t (swapPerm n v)) := by rw [Finset.sum_neg_distrib]
        _ = -(∑ u : Fin n, iterState lam γ σ ω ζ t u) := by
            congr 1; exact Equiv.sum_comp (swapPerm n) (fun u => iterState lam γ σ ω ζ t u)
    change (∑ v : Fin n, iterState lam γ σ (permEdge (swapPerm n) ω) (flipKick (swapPerm n) ζ) t v) / (n : ℝ) = _
    rw [hsum, neg_div]
  have hEq : ∑ p : (EdgeIdx n → Bool) × KickBits T n,
      (∑ v : Fin n, iterState lam γ σ p.1 p.2 t v) / (n : ℝ) =
      ∑ p : (EdgeIdx n → Bool) × KickBits T n,
        -((∑ v : Fin n, iterState lam γ σ p.1 p.2 t v) / (n : ℝ)) := by
    calc _ = ∑ p, (∑ v, iterState lam γ σ (inv p).1 (inv p).2 t v) / (n : ℝ) :=
          (Equiv.sum_comp inv _).symm
      _ = _ := Finset.sum_congr rfl fun p _ => hneg p
  rw [Finset.sum_neg_distrib] at hEq
  linarith

/- #### Operator-Norm Helper & `C^2` Backpropagation Efron–Stein Variance Bound -/

/-- `‖iterGrad ω x‖_2^2 ≤ M^2 ‖x‖_2^2` whenever `‖A(ω)/√n‖_op ≤ M`. -/
lemma op_norm_matvec_sq {n : ℕ} (hn : 1 ≤ n) (ω : EdgeIdx n → Bool) {M : ℝ} (_hM : 0 ≤ M)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ M * Real.sqrt (n : ℝ))
    (x : Fin n → ℝ) :
    ∑ i : Fin n, (iterGrad ω x i) ^ 2 ≤ M ^ 2 * ∑ j : Fin n, (x j) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  set y : Fin n → ℝ := iterGrad ω x
  set sy := ∑ i : Fin n, (y i) ^ 2
  set sx := ∑ j : Fin n, (x j) ^ 2
  by_cases hsy : sy = 0
  · rw [hsy]; exact mul_nonneg (sq_nonneg M) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  by_cases hsx : sx = 0
  · have hx0 : ∀ j, x j = 0 := fun j => by
      have : (x j) ^ 2 ≤ 0 := (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans hsx.le
      nlinarith
    have hy0 : ∀ i, y i = 0 := fun i => by simp [y, iterGrad, hx0]
    have : sy = 0 := Finset.sum_eq_zero fun i _ => by simp [hy0 i]
    exact absurd this hsy
  have hsy_pos : 0 < sy := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hsy)
  have hsx_pos : 0 < sx := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hsx)
  let yn : Fin n → ℝ := fun i => y i / Real.sqrt sy
  let xn : Fin n → ℝ := fun j => x j / Real.sqrt sx
  have hyn : ∑ i, (yn i) ^ 2 ≤ 1 := by
    simp only [yn, div_pow, Real.sq_sqrt hsy_pos.le, ← Finset.sum_div]; rw [div_self hsy_pos.ne']
  have hxn : ∑ j, (xn j) ^ 2 ≤ 1 := by
    simp only [xn, div_pow, Real.sq_sqrt hsx_pos.le, ← Finset.sum_div]; rw [div_self hsx_pos.ne']
  have hbd := hop yn xn hyn hxn
  have hbilin : (∑ i : Fin n, ∑ j : Fin n, yn i * adjSign ω i j * xn j) =
      sy * Real.sqrt (n : ℝ) / (Real.sqrt sy * Real.sqrt sx) := by
    have hsum : ∑ i : Fin n, ∑ j : Fin n, y i * adjSign ω i j * x j = sy * Real.sqrt (n : ℝ) := by
      have h1 : ∀ i : Fin n, ∑ j : Fin n, y i * adjSign ω i j * x j = (y i) ^ 2 * Real.sqrt (n : ℝ) := by
        intro i
        have heq : ∑ j : Fin n, y i * adjSign ω i j * x j = y i * ∑ j : Fin n, adjSign ω i j * x j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        have hy_def : ∑ j : Fin n, adjSign ω i j * x j = y i * Real.sqrt (n : ℝ) := by
          simp only [y, iterGrad]; field_simp
        rw [hy_def]; ring
      simp_rw [h1, ← Finset.sum_mul]; rfl
    have hfac : ∑ i : Fin n, ∑ j : Fin n, yn i * adjSign ω i j * xn j =
        (∑ i : Fin n, ∑ j : Fin n, y i * adjSign ω i j * x j) / (Real.sqrt sy * Real.sqrt sx) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => by simp only [yn, xn]; field_simp
    rw [hfac, hsum]
  rw [hbilin, abs_of_pos (by positivity), div_le_iff₀ (by positivity)] at hbd
  have hle_sqrt : Real.sqrt sy ≤ M * Real.sqrt sx := by
    have h1 : sy = Real.sqrt sy * Real.sqrt sy := (Real.mul_self_sqrt hsy_pos.le).symm
    have hpos : 0 < Real.sqrt sy * Real.sqrt (n : ℝ) := by positivity
    have h2 : Real.sqrt sy * (Real.sqrt sy * Real.sqrt (n : ℝ)) ≤
        (M * Real.sqrt sx) * (Real.sqrt sy * Real.sqrt (n : ℝ)) := by
      rw [← mul_assoc, ← h1]
      linarith [hbd, show M * Real.sqrt (n : ℝ) * (Real.sqrt sy * Real.sqrt sx) =
        M * Real.sqrt sx * (Real.sqrt sy * Real.sqrt (n : ℝ)) by ring]
    exact le_of_mul_le_mul_right h2 hpos
  have hsq_le := pow_le_pow_left₀ (Real.sqrt_nonneg sy) hle_sqrt 2
  rw [mul_pow, Real.sq_sqrt hsy_pos.le, Real.sq_sqrt hsx_pos.le] at hsq_le
  exact hsq_le

/-- Symmetry of `iterGrad`: `⟨u, iterGrad ω v⟩ = ⟨iterGrad ω u, v⟩`. -/
lemma sum_mul_iterGrad_comm {n : ℕ} (ω : EdgeIdx n → Bool) (u v : Fin n → ℝ) :
    ∑ i : Fin n, u i * iterGrad ω v i = ∑ j : Fin n, iterGrad ω u j * v j := by
  simp only [iterGrad, mul_div_assoc', div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [adjSign_symm]; ring

/-- Backpropagation adjoint vectors `bpLam t k` representing `λ_{t - k}` for `0 ≤ k ≤ t`. -/
noncomputable def bpLam {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (t : ℕ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1 / (n : ℝ)
  | k + 1 =>
    let s := t - (k + 1)
    let x := iterState lam γ σ ω ζ s
    let xt := iterKick γ σ ζ s x
    let u := fun v => xt v + (1 / 20 : ℝ) * iterGrad ω xt v
    let lamNext := bpLam lam γ σ ω ζ t k
    let mu := fun w => psiDeriv lam (u w) * lamNext w
    let nu := fun w => mu w + (1 / 20 : ℝ) * iterGrad ω mu w
    fun v => (1 + σ * chiDeriv γ (x v) * kickVal ζ s v) * nu v

noncomputable def bpMu {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (t k : ℕ) (w : Fin n) : ℝ :=
  let s := t - (k + 1)
  let x := iterState lam γ σ ω ζ s
  let xt := iterKick γ σ ζ s x
  let u := xt w + (1 / 20 : ℝ) * iterGrad ω xt w
  psiDeriv lam u * bpLam lam γ σ ω ζ t k w

noncomputable def bpNu {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (t k : ℕ) (w : Fin n) : ℝ :=
  let mu := bpMu lam γ σ ω ζ t k
  mu w + (1 / 20 : ℝ) * iterGrad ω mu w

lemma bpLam_succ_eq {T n : ℕ} (lam γ σ : ℝ) (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (t k : ℕ) (v : Fin n) :
    bpLam lam γ σ ω ζ t (k + 1) v =
      (1 + σ * chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v) *
        kickVal ζ (t - (k + 1)) v) * bpNu lam γ σ ω ζ t k v := rfl

/-- `ℓ_2` norm bounds on the backpropagation adjoint vectors on the good operator-norm event. -/
lemma bpLam_norm_sq_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t : ℕ) :
    ∀ k : ℕ, ∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2 ≤ (36 : ℝ) ^ k / (n : ℝ)
  | 0 => by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    simp only [bpLam, pow_zero, div_pow, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    exact le_rfl
  | k + 1 => by
    have ih := bpLam_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k
    have hmu : ∑ w : Fin n, (bpMu lam γ σ ω ζ t k w) ^ 2 ≤
        ∑ w : Fin n, (bpLam lam γ σ ω ζ t k w) ^ 2 := by
      refine Finset.sum_le_sum fun w _ => ?_
      simp only [bpMu, mul_pow]
      set z := iterKick γ σ ζ (t - (k + 1)) (iterState lam γ σ ω ζ (t - (k + 1))) w +
        (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ (t - (k + 1)) (iterState lam γ σ ω ζ (t - (k + 1)))) w
      have hpd := psiDeriv_bounds hlam z
      have hsq : (psiDeriv lam z) ^ 2 ≤ 1 := by nlinarith only [hpd.1, hpd.2]
      exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans (by linarith)
    have hgrad := op_norm_matvec_sq hn ω (by norm_num : (0 : ℝ) ≤ 20) hop (bpMu lam γ σ ω ζ t k)
    have hnu : ∑ w : Fin n, (bpNu lam γ σ ω ζ t k w) ^ 2 ≤
        4 * ∑ w : Fin n, (bpLam lam γ σ ω ζ t k w) ^ 2 := by
      have hpw : ∑ w : Fin n, (bpNu lam γ σ ω ζ t k w) ^ 2 ≤
          2 * ∑ w : Fin n, (bpMu lam γ σ ω ζ t k w) ^ 2 +
          2 * (1 / 400 : ℝ) * ∑ w : Fin n, (iterGrad ω (bpMu lam γ σ ω ζ t k) w) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun w _ => ?_
        simp only [bpNu]
        nlinarith [sq_nonneg (bpMu lam γ σ ω ζ t k w - (1 / 20 : ℝ) * iterGrad ω (bpMu lam γ σ ω ζ t k) w)]
      linarith [hpw, hgrad, hmu]
    have hfac : ∀ v : Fin n,
        (1 + σ * chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v) *
          kickVal ζ (t - (k + 1)) v) ^ 2 ≤ 9 := by
      intro v
      have hcd := abs_chiDeriv_le hγ0 hγ1 (iterState lam γ σ ω ζ (t - (k + 1)) v)
      have hW := abs_kickVal_lt_two ζ (t - (k + 1)) v
      have hprod : |σ * chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v) *
          kickVal ζ (t - (k + 1)) v| ≤ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
        have h1 : σ * |chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v)| ≤ 1 := by
          calc σ * |chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v)|
              ≤ (γ / 8) * (8 / γ) := mul_le_mul hσ hcd (abs_nonneg _) (by positivity)
            _ = 1 := by field_simp
        calc σ * |chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v)| *
              |kickVal ζ (t - (k + 1)) v|
            ≤ 1 * 2 := mul_le_mul h1 hW.le (abs_nonneg _) zero_le_one
          _ = 2 := one_mul 2
      have habs := abs_le.mp hprod
      nlinarith [habs.1, habs.2]
    calc ∑ v : Fin n, (bpLam lam γ σ ω ζ t (k + 1) v) ^ 2
        = ∑ v : Fin n, (1 + σ * chiDeriv γ (iterState lam γ σ ω ζ (t - (k + 1)) v) *
            kickVal ζ (t - (k + 1)) v) ^ 2 * (bpNu lam γ σ ω ζ t k v) ^ 2 := by
          refine Finset.sum_congr rfl fun v _ => by rw [bpLam_succ_eq, mul_pow]
      _ ≤ ∑ v : Fin n, 9 * (bpNu lam γ σ ω ζ t k v) ^ 2 :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hfac v) (sq_nonneg _)
      _ = 9 * ∑ v : Fin n, (bpNu lam γ σ ω ζ t k v) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 36 * ∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2 := by linarith [hnu]
      _ ≤ 36 * ((36 : ℝ) ^ k / (n : ℝ)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (36 : ℝ) ^ (k + 1) / (n : ℝ) := by rw [pow_succ']; ring

lemma bpMu_norm_sq_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t k : ℕ) :
    ∑ w : Fin n, (bpMu lam γ σ ω ζ t k w) ^ 2 ≤ (36 : ℝ) ^ k / (n : ℝ) := by
  have hmu : ∑ w : Fin n, (bpMu lam γ σ ω ζ t k w) ^ 2 ≤
      ∑ w : Fin n, (bpLam lam γ σ ω ζ t k w) ^ 2 := by
    refine Finset.sum_le_sum fun w _ => ?_
    simp only [bpMu, mul_pow]
    set z := iterKick γ σ ζ (t - (k + 1)) (iterState lam γ σ ω ζ (t - (k + 1))) w +
      (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ (t - (k + 1)) (iterState lam γ σ ω ζ (t - (k + 1)))) w
    have hpd := psiDeriv_bounds hlam z
    have hsq : (psiDeriv lam z) ^ 2 ≤ 1 := by nlinarith only [hpd.1, hpd.2]
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans (by linarith)
  exact hmu.trans (bpLam_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k)

lemma bpNu_norm_sq_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t k : ℕ) :
    ∑ w : Fin n, (bpNu lam γ σ ω ζ t k w) ^ 2 ≤ 4 * (36 : ℝ) ^ k / (n : ℝ) := by
  have hmu := bpMu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k
  have hgrad := op_norm_matvec_sq hn ω (by norm_num : (0 : ℝ) ≤ 20) hop (bpMu lam γ σ ω ζ t k)
  have hpw : ∑ w : Fin n, (bpNu lam γ σ ω ζ t k w) ^ 2 ≤
      2 * ∑ w : Fin n, (bpMu lam γ σ ω ζ t k w) ^ 2 +
      2 * (1 / 400 : ℝ) * ∑ w : Fin n, (iterGrad ω (bpMu lam γ σ ω ζ t k) w) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    simp only [bpNu]
    nlinarith [sq_nonneg (bpMu lam γ σ ω ζ t k w - (1 / 20 : ℝ) * iterGrad ω (bpMu lam γ σ ω ζ t k) w)]
  have h4 : 4 * ((36 : ℝ) ^ k / (n : ℝ)) = 4 * (36 : ℝ) ^ k / (n : ℝ) := by ring
  linarith [hpw, hgrad, hmu, h4]

/-- Helper: `∑ a_i^2 ≤ (∑ |a_i|)^2` for any finite real vector. -/
lemma sum_sq_le_sq_sum_abs {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∑ i : ι, (a i) ^ 2 ≤ (∑ i : ι, |a i|) ^ 2 := by
  have hle : ∀ i : ι, (a i) ^ 2 ≤ |a i| * (∑ j : ι, |a j|) := fun i => by
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j : ι => |a j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
  calc ∑ i : ι, (a i) ^ 2
      ≤ ∑ i : ι, |a i| * (∑ j : ι, |a j|) := Finset.sum_le_sum fun i _ => hle i
    _ = (∑ i : ι, |a i|) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- Exact one-step backpropagation identity linking `⟨λ_{s+1}, dx_{s+1}⟩` and `⟨λ_s, dx_s⟩`. -/
lemma backprop_step_identity {T n : ℕ} (lam γ σ : ℝ)
    (ω ω' : EdgeIdx n → Bool) (ζ ζ' : KickBits T n) (t k : ℕ) (_hk : k < t) :
    let s := t - (k + 1)
    let x := iterState lam γ σ ω ζ s
    let x' := iterState lam γ σ ω' ζ' s
    let dx := fun v => x' v - x v
    let xt := iterKick γ σ ζ s x
    let xt' := iterKick γ σ ζ' s x'
    let dxt := fun v => xt' v - xt v
    let u := fun v => xt v + (1 / 20 : ℝ) * iterGrad ω xt v
    let u' := fun v => xt' v + (1 / 20 : ℝ) * iterGrad ω' xt' v
    let du := fun v => u' v - u v
    let r1 := fun v => (iterState lam γ σ ω' ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
      psiDeriv lam (u v) * du v
    let r2 := fun v => σ * (chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v) * kickVal ζ s v
    let dA0 := fun v => (1 / 20 : ℝ) * (iterGrad ω' xt v - iterGrad ω xt v)
    let dA1 := fun v => (1 / 20 : ℝ) * (iterGrad ω' dxt v - iterGrad ω dxt v)
    let dW0 := fun v => σ * chi γ (x v) * (kickVal ζ' s v - kickVal ζ s v)
    let dW1 := fun v => σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ' s v - kickVal ζ s v)
    ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
        (iterState lam γ σ ω' ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
      ∑ v : Fin n, bpLam lam γ σ ω ζ t (k + 1) v * dx v =
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) +
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * (r2 v + dW1 v)) +
      (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) := by
  intro s x x' dx xt xt' dxt u u' du r1 r2 dA0 dA1 dW0 dW1
  have hdu : ∀ v, du v = dxt v + (1 / 20 : ℝ) * iterGrad ω dxt v + dA0 v + dA1 v := by
    intro v
    have hgrad_lin : iterGrad ω' xt' v - iterGrad ω xt v =
        iterGrad ω dxt v + (iterGrad ω' xt v - iterGrad ω xt v) +
        (iterGrad ω' dxt v - iterGrad ω dxt v) := by
      have hlin' : iterGrad ω' xt' v = iterGrad ω' xt v + iterGrad ω' dxt v := by
        simp only [iterGrad, dxt, ← add_div, ← Finset.sum_add_distrib]
        congr 1; refine Finset.sum_congr rfl fun w _ => by ring
      linarith [hlin']
    simp only [du, u', u, dxt, dA0, dA1]
    linarith [hgrad_lin]
  have hdxt : ∀ v, dxt v =
      (1 + σ * chiDeriv γ (x v) * kickVal ζ s v) * dx v + r2 v + dW0 v + dW1 v := by
    intro v
    simp only [dxt, xt', xt, iterKick, dx, r2, dW0, dW1]; ring
  have hstep1 : ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
        (iterState lam γ σ ω' ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) =
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * du v) +
      (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [bpMu, r1, s, x, xt, u]; ring
  have hstep2 : ∑ v : Fin n, bpMu lam γ σ ω ζ t k v * du v =
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dxt v) +
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) := by
    have hsym := sum_mul_iterGrad_comm ω (bpMu lam γ σ ω ζ t k) dxt
    have h1 : ∑ v : Fin n, bpMu lam γ σ ω ζ t k v * du v =
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dxt v) +
        (1 / 20 : ℝ) * (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * iterGrad ω dxt v) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by rw [hdu v]; ring
    have h2 : ∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dxt v =
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dxt v) +
        (1 / 20 : ℝ) * (∑ v : Fin n, iterGrad ω (bpMu lam γ σ ω ζ t k) v * dxt v) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by simp only [bpNu]; ring
    linarith [h1, h2, hsym]
  have hstep3 : ∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dxt v =
      (∑ v : Fin n, bpLam lam γ σ ω ζ t (k + 1) v * dx v) +
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * (r2 v + dW1 v)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hdxt v, bpLam_succ_eq]
    simp only [s, x]; ring
  linarith [hstep1, hstep2, hstep3]

/-- Helper: Cauchy–Schwarz bound `|∑ v, a v * b v| ≤ √(∑ a^2) * √(∑ b^2)`. -/
lemma abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |∑ i : ι, a i * b i| ≤ Real.sqrt (∑ i : ι, (a i) ^ 2) * Real.sqrt (∑ i : ι, (b i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h1 : (∑ i : ι, a i * b i) ^ 2 ≤
      (Real.sqrt (∑ i : ι, (a i) ^ 2) * Real.sqrt (∑ i : ι, (b i) ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact hcs
  have hrhs : 0 ≤ Real.sqrt (∑ i : ι, (a i) ^ 2) * Real.sqrt (∑ i : ι, (b i) ^ 2) := by positivity
  rw [abs_le]
  constructor <;> nlinarith [h1, hrhs]

/-- Single edge-flip sensitivity bound on the good operator-norm event via `C^2` backpropagation. -/
lemma edge_flip_single_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t : ℕ) (e : EdgeIdx n) :
    let F : (EdgeIdx n → Bool) → ℝ := fun ω' => (∑ v : Fin n, iterState lam γ σ ω' ζ t v) / (n : ℝ)
    let C_rem : ℝ := (t : ℝ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t *
      (1 + 100 / γ + 1 / Real.sqrt lam)
    |F (Function.update ω e (!ω e)) - F ω| ≤
      (1 / (10 * Real.sqrt (n : ℝ))) *
        (∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|)) +
      C_rem / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  intro F C_rem
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  set ω' := Function.update ω e (!ω e)
  have hadj_diff : ∀ u v : Fin n,
      adjSign ω' u v - adjSign ω u v =
        if (u = e.1.1 ∧ v = e.1.2) ∨ (u = e.1.2 ∧ v = e.1.1) then
          if ω e then (-2 : ℝ) else 2
        else 0 := by
    intro u v
    rcases e with ⟨⟨a, b⟩, hab⟩
    unfold adjSign
    by_cases h1 : u = a ∧ v = b
    · rcases h1 with ⟨rfl, rfl⟩
      simp only [ω', dif_pos hab, Function.update_self, true_and, true_or, ite_true]
      cases ω ⟨(u, v), hab⟩ <;> norm_num
    · by_cases h2 : u = b ∧ v = a
      · rcases h2 with ⟨rfl, rfl⟩
        have hnot : ¬ u < v := lt_asymm hab
        simp only [ω', dif_neg hnot, dif_pos hab, Function.update_self, and_self, or_true, ite_true]
        cases ω ⟨(v, u), hab⟩ <;> norm_num
      · simp only [if_neg (not_or.mpr ⟨h1, h2⟩)]
        rcases lt_trichotomy u v with hlt | rfl | hgt
        · have hne : (⟨(u, v), hlt⟩ : EdgeIdx n) ≠ ⟨(a, b), hab⟩ := by
            intro heq; apply h1; exact Prod.mk.inj (congrArg Subtype.val heq)
          simp only [ω', dif_pos hlt, Function.update_of_ne hne, sub_self]
        · simp
        · have hnot : ¬ u < v := lt_asymm hgt
          have hne : (⟨(v, u), hgt⟩ : EdgeIdx n) ≠ ⟨(a, b), hab⟩ := by
            intro heq; apply h2
            have hpair := Prod.mk.inj (congrArg Subtype.val heq)
            exact ⟨hpair.2, hpair.1⟩
          simp only [ω', dif_neg hnot, dif_pos hgt, Function.update_of_ne hne, sub_self]
  have hgrad_diff_pt : ∀ (z : Fin n → ℝ) (v : Fin n),
      |iterGrad ω' z v - iterGrad ω z v| ≤
        (if v = e.1.1 then 2 * |z e.1.2| else 0) / Real.sqrt (n : ℝ) +
        (if v = e.1.2 then 2 * |z e.1.1| else 0) / Real.sqrt (n : ℝ) := by
    intro z v
    have hne_ab : e.1.1 ≠ e.1.2 := e.2.ne
    have hsub : iterGrad ω' z v - iterGrad ω z v =
        (∑ w : Fin n, (adjSign ω' v w - adjSign ω v w) * z w) / Real.sqrt (n : ℝ) := by
      simp only [iterGrad, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun w _ => by ring
    rw [hsub, abs_div, abs_of_pos hsq_pos, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hsq_pos.le
    by_cases hva : v = e.1.1
    · rw [hva]
      have hsum_eq : ∑ w : Fin n, (adjSign ω' e.1.1 w - adjSign ω e.1.1 w) * z w =
          (if ω e then (-2 : ℝ) else 2) * z e.1.2 := by
        rw [Finset.sum_eq_single e.1.2]
        · simp [hadj_diff]
        · intro w _ hwb
          rw [hadj_diff, if_neg (by tauto), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum_eq, abs_mul, if_pos rfl, if_neg hne_ab, add_zero]
      have h2 : |if ω e then (-2 : ℝ) else 2| = 2 := by cases ω e <;> norm_num
      rw [h2]
    · by_cases hvb : v = e.1.2
      · rw [hvb]
        have hsum_eq : ∑ w : Fin n, (adjSign ω' e.1.2 w - adjSign ω e.1.2 w) * z w =
            (if ω e then (-2 : ℝ) else 2) * z e.1.1 := by
          rw [Finset.sum_eq_single e.1.1]
          · simp [hadj_diff]
          · intro w _ hwa
            rw [hadj_diff, if_neg (by tauto), zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum_eq, abs_mul, if_neg hne_ab.symm, if_pos rfl, zero_add]
        have h2 : |if ω e then (-2 : ℝ) else 2| = 2 := by cases ω e <;> norm_num
        rw [h2]
      · have hsum_eq : ∑ w : Fin n, (adjSign ω' v w - adjSign ω v w) * z w = 0 :=
          Finset.sum_eq_zero fun w _ => by
            rw [hadj_diff]
            have hnot : ¬ ((v = e.1.1 ∧ w = e.1.2) ∨ (v = e.1.2 ∧ w = e.1.1)) := by tauto
            simp [hnot]
        rw [hsum_eq, abs_zero, if_neg hva, if_neg hvb, add_zero]
  have hgrad_diff_sq : ∀ z : Fin n → ℝ,
      ∑ v : Fin n, (iterGrad ω' z v - iterGrad ω z v) ^ 2 ≤
        4 * ((z e.1.1) ^ 2 + (z e.1.2) ^ 2) / (n : ℝ) := by
    intro z
    have hne_ab : e.1.1 ≠ e.1.2 := e.2.ne
    have hpw : ∀ v : Fin n, (iterGrad ω' z v - iterGrad ω z v) ^ 2 ≤
        (if v = e.1.1 then 4 * (z e.1.2) ^ 2 / (n : ℝ) else 0) +
        (if v = e.1.2 then 4 * (z e.1.1) ^ 2 / (n : ℝ) else 0) := by
      intro v
      have h1 := hgrad_diff_pt z v
      by_cases hva : v = e.1.1
      · rw [hva] at h1 ⊢
        simp only [ite_true, if_neg hne_ab, zero_div, add_zero] at h1 ⊢
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs, div_pow, mul_pow, sq_abs, Real.sq_sqrt hn_pos.le] at h2
        linarith [h2, show (2 : ℝ) ^ 2 = 4 by norm_num]
      · by_cases hvb : v = e.1.2
        · rw [hvb] at h1 ⊢
          simp only [if_neg hne_ab.symm, ite_true, zero_div, zero_add] at h1 ⊢
          have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          rw [sq_abs, div_pow, mul_pow, sq_abs, Real.sq_sqrt hn_pos.le] at h2
          linarith [h2, show (2 : ℝ) ^ 2 = 4 by norm_num]
        · simp only [if_neg hva, if_neg hvb, zero_div, add_zero] at h1 ⊢
          have hz : iterGrad ω' z v - iterGrad ω z v = 0 :=
            abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
          simp [hz]
    calc ∑ v : Fin n, (iterGrad ω' z v - iterGrad ω z v) ^ 2
        ≤ ∑ v : Fin n, ((if v = e.1.1 then 4 * (z e.1.2) ^ 2 / (n : ℝ) else 0) +
            (if v = e.1.2 then 4 * (z e.1.1) ^ 2 / (n : ℝ) else 0)) :=
          Finset.sum_le_sum fun v _ => hpw v
      _ = 4 * (z e.1.2) ^ 2 / (n : ℝ) + 4 * (z e.1.1) ^ 2 / (n : ℝ) := by
          rw [Finset.sum_add_distrib]; simp
      _ = 4 * ((z e.1.1) ^ 2 + (z e.1.2) ^ 2) / (n : ℝ) := by ring
  have hdxt_pw : ∀ (s : ℕ) (v : Fin n),
      |iterKick γ σ ζ s (iterState lam γ σ ω' ζ s) v -
        iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v| ≤
        3 * |iterState lam γ σ ω' ζ s v - iterState lam γ σ ω ζ s v| := by
    intro s v
    set x := iterState lam γ σ ω ζ s
    set x' := iterState lam γ σ ω' ζ s
    have heq : iterKick γ σ ζ s x' v - iterKick γ σ ζ s x v =
        (x' v - x v) + σ * (chi γ (x' v) - chi γ (x v)) * kickVal ζ s v := by
      simp only [iterKick]; ring
    rw [heq]
    have h1 : |σ * (chi γ (x' v) - chi γ (x v)) * kickVal ζ s v| ≤ 2 * |x' v - x v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
      have hc := chi_lip hγ0 hγ1 (x' v) (x v)
      have hW := abs_kickVal_lt_two ζ s v
      have hsc : σ * |chi γ (x' v) - chi γ (x v)| ≤ |x' v - x v| := by
        calc σ * |chi γ (x' v) - chi γ (x v)|
            ≤ (γ / 8) * ((8 / γ) * |x' v - x v|) :=
              mul_le_mul hσ hc (abs_nonneg _) (by positivity)
          _ = |x' v - x v| := by field_simp
      calc σ * |chi γ (x' v) - chi γ (x v)| * |kickVal ζ s v|
          ≤ |x' v - x v| * 2 := mul_le_mul hsc hW.le (abs_nonneg _) (abs_nonneg _)
        _ = 2 * |x' v - x v| := mul_comm _ _
    exact (abs_add_le _ _).trans (by linarith)
  have hdu_from_dx : ∀ s : ℕ,
      ∑ v : Fin n, ((iterKick γ σ ζ s (iterState lam γ σ ω' ζ s) v +
          (1 / 20 : ℝ) * iterGrad ω' (iterKick γ σ ζ s (iterState lam γ σ ω' ζ s)) v) -
          (iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v +
          (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s (iterState lam γ σ ω ζ s)) v)) ^ 2 ≤
        54 * (∑ v : Fin n, (iterState lam γ σ ω' ζ s v - iterState lam γ σ ω ζ s v) ^ 2) + 1 / (n : ℝ) := by
    intro s
    set x := iterState lam γ σ ω ζ s
    set x' := iterState lam γ σ ω' ζ s
    set xt := iterKick γ σ ζ s x
    set xt' := iterKick γ σ ζ s x'
    have hdxt_sq : ∑ v : Fin n, (xt' v - xt v) ^ 2 ≤ 9 * ∑ v : Fin n, (x' v - x v) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hdxt_pw s v) 2
      rw [sq_abs, mul_pow, sq_abs] at h1
      linarith [h1, show (3 : ℝ) ^ 2 = 9 by norm_num]
    have hgrad_dxt := op_norm_matvec_sq hn ω (by norm_num : (0 : ℝ) ≤ 20) hop (fun v => xt' v - xt v)
    have hgrad_diff := hgrad_diff_sq xt'
    have hxt'_bd : (xt' e.1.1) ^ 2 + (xt' e.1.2) ^ 2 ≤ 2 := by
      have ha := abs_iterKick_lt_one hγ0 hγ1 hσ0 hσ ζ s x' e.1.1 (abs_iterState_lt_one hlam ω' ζ s e.1.1)
      have hb := abs_iterKick_lt_one hγ0 hγ1 hσ0 hσ ζ s x' e.1.2 (abs_iterState_lt_one hlam ω' ζ s e.1.2)
      nlinarith only [(abs_lt.mp ha).1, (abs_lt.mp ha).2, (abs_lt.mp hb).1, (abs_lt.mp hb).2]
    have hpw : ∀ v : Fin n,
        ((xt' v + (1 / 20 : ℝ) * iterGrad ω' xt' v) -
          (xt v + (1 / 20 : ℝ) * iterGrad ω xt v)) ^ 2 ≤
        3 * (xt' v - xt v) ^ 2 +
        (3 / 400 : ℝ) * (iterGrad ω (fun w => xt' w - xt w) v) ^ 2 +
        (3 / 400 : ℝ) * (iterGrad ω' xt' v - iterGrad ω xt' v) ^ 2 := by
      intro v
      have hdecomp : (xt' v + (1 / 20 : ℝ) * iterGrad ω' xt' v) -
          (xt v + (1 / 20 : ℝ) * iterGrad ω xt v) =
          (xt' v - xt v) + (1 / 20 : ℝ) * iterGrad ω (fun w => xt' w - xt w) v +
          (1 / 20 : ℝ) * (iterGrad ω' xt' v - iterGrad ω xt' v) := by
        have hlin : iterGrad ω xt' v - iterGrad ω xt v = iterGrad ω (fun w => xt' w - xt w) v := by
          simp only [iterGrad, ← sub_div, ← Finset.sum_sub_distrib]
          congr 1; refine Finset.sum_congr rfl fun w _ => by ring
        linarith [hlin]
      rw [hdecomp]
      set a := xt' v - xt v
      set b := (1 / 20 : ℝ) * iterGrad ω (fun w => xt' w - xt w) v
      set c := (1 / 20 : ℝ) * (iterGrad ω' xt' v - iterGrad ω xt' v)
      have h3 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have hb2 : 3 * b ^ 2 = (3 / 400 : ℝ) * (iterGrad ω (fun w => xt' w - xt w) v) ^ 2 := by
        simp only [b]; ring
      have hc2 : 3 * c ^ 2 = (3 / 400 : ℝ) * (iterGrad ω' xt' v - iterGrad ω xt' v) ^ 2 := by
        simp only [c]; ring
      linarith [h3, hb2, hc2]
    have hsum_le : ∑ v : Fin n,
        ((xt' v + (1 / 20 : ℝ) * iterGrad ω' xt' v) -
          (xt v + (1 / 20 : ℝ) * iterGrad ω xt v)) ^ 2 ≤
        3 * ∑ v : Fin n, (xt' v - xt v) ^ 2 +
        (3 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω (fun w => xt' w - xt w) v) ^ 2 +
        (3 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω' xt' v - iterGrad ω xt' v) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ => hpw v
    have hgd : (3 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω' xt' v - iterGrad ω xt' v) ^ 2 ≤ 1 / (n : ℝ) := by
      have h1 : ∑ v : Fin n, (iterGrad ω' xt' v - iterGrad ω xt' v) ^ 2 ≤ 8 * (1 / (n : ℝ)) :=
        hgrad_diff.trans (by rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) hn_pos.le)
      linarith [h1, div_nonneg zero_le_one hn_pos.le]
    linarith [hsum_le, hgrad_dxt, hdxt_sq, hgd]
  have hfwd : ∀ s : ℕ,
      ∑ v : Fin n, (iterState lam γ σ ω' ζ s v - iterState lam γ σ ω ζ s v) ^ 2 ≤
        (64 : ℝ) ^ s / (n : ℝ) := by
    intro s
    induction s with
    | zero => simp [iterState]
    | succ s ih =>
      have hlip_sum : ∑ v : Fin n,
          (iterState lam γ σ ω' ζ (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) ^ 2 ≤
          ∑ v : Fin n,
            ((iterKick γ σ ζ s (iterState lam γ σ ω' ζ s) v +
              (1 / 20 : ℝ) * iterGrad ω' (iterKick γ σ ζ s (iterState lam γ σ ω' ζ s)) v) -
            (iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v +
              (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s (iterState lam γ σ ω ζ s)) v)) ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hl := psi_lip hlam
          (iterKick γ σ ζ s (iterState lam γ σ ω' ζ s) v +
            (1 / 20 : ℝ) * iterGrad ω' (iterKick γ σ ζ s (iterState lam γ σ ω' ζ s)) v)
          (iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v +
            (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s (iterState lam γ σ ω ζ s)) v)
        have h2 := pow_le_pow_left₀ (abs_nonneg _) hl 2
        rwa [sq_abs, sq_abs] at h2
      have hdu := hdu_from_dx s
      have hpow_ge : (1 : ℝ) ≤ (64 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      have h1n : 1 / (n : ℝ) ≤ (64 : ℝ) ^ s / (n : ℝ) :=
        div_le_div_of_nonneg_right hpow_ge hn_pos.le
      have h64 : (64 : ℝ) ^ (s + 1) / (n : ℝ) = 64 * ((64 : ℝ) ^ s / (n : ℝ)) := by
        rw [pow_succ']; ring
      have hnn : 0 ≤ (64 : ℝ) ^ s / (n : ℝ) := by positivity
      linarith [hlip_sum, hdu, ih, h1n, h64, hnn]
  -- Telescope over `k ∈ Finset.range t`.
  let g : ℕ → ℝ := fun k =>
    ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
      (iterState lam γ σ ω' ζ (t - k) v - iterState lam γ σ ω ζ (t - k) v)
  have hg0 : g 0 = F ω' - F ω := by
    simp only [g, bpLam, Nat.sub_zero, F, one_div_mul_eq_div, ← Finset.sum_div,
      Finset.sum_sub_distrib, sub_div]
  have hgt : g t = 0 := by simp [g, iterState]
  have htele : F ω' - F ω = ∑ k ∈ Finset.range t, (g k - g (k + 1)) := by
    have h1 := Finset.sum_range_sub' g t
    linarith [h1, hg0, hgt]
  have hstep_bd : ∀ k ∈ Finset.range t,
      |g k - g (k + 1)| ≤
        (1 / (10 * Real.sqrt (n : ℝ))) *
          (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|) +
        (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
          ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    intro k hk
    have hklt : k < t := Finset.mem_range.mp hk
    set s := t - (k + 1)
    have hs1 : s + 1 = t - k := by omega
    have hst : s < t := by omega
    have hgk_eq : g k - g (k + 1) =
        ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
          (iterState lam γ σ ω' ζ (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
        ∑ v : Fin n, bpLam lam γ σ ω ζ t (k + 1) v *
          (iterState lam γ σ ω' ζ s v - iterState lam γ σ ω ζ s v) := by
      simp only [g, s, hs1]
    rw [hgk_eq, backprop_step_identity lam γ σ ω ω' ζ ζ t k hklt]
    set x := iterState lam γ σ ω ζ s
    set x' := iterState lam γ σ ω' ζ s
    set dx := fun v => x' v - x v
    set xt := iterKick γ σ ζ s x
    set xt' := iterKick γ σ ζ s x'
    set dxt := fun v => xt' v - xt v
    set u := fun v => xt v + (1 / 20 : ℝ) * iterGrad ω xt v
    set u' := fun v => xt' v + (1 / 20 : ℝ) * iterGrad ω' xt' v
    set du := fun v => u' v - u v
    set r1 := fun v => (iterState lam γ σ ω' ζ (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
      psiDeriv lam (u v) * du v
    set r2 := fun v => σ * (chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v) * kickVal ζ s v
    set dA0 := fun v => (1 / 20 : ℝ) * (iterGrad ω' xt v - iterGrad ω xt v)
    set dA1 := fun v => (1 / 20 : ℝ) * (iterGrad ω' dxt v - iterGrad ω dxt v)
    have hrhs_clean :
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * (σ * chi γ (x v) * (kickVal ζ s v - kickVal ζ s v))) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v *
          (r2 v + σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ s v - kickVal ζ s v))) +
        (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) =
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v) +
        (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) := by
      simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    change |((∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * (σ * chi γ (x v) * (kickVal ζ s v - kickVal ζ s v))) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v *
          (r2 v + σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ s v - kickVal ζ s v))) +
        (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v))| ≤ _
    rw [hrhs_clean]
    have hpow6 : (36 : ℝ) ^ k ≤ (36 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hklt.le
    have hpow64 : (64 : ℝ) ^ s ≤ (64 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst.le
    have hpow64_s1 : (64 : ℝ) ^ (s + 1) ≤ (64 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst
    have h36_sq : (36 : ℝ) ^ t = ((6 : ℝ) ^ t) ^ 2 := by
      calc (36 : ℝ) ^ t = ((6 : ℝ) ^ 2) ^ t := by norm_num
        _ = ((6 : ℝ) ^ t) ^ 2 := by rw [← pow_mul, mul_comm 2 t, pow_mul]
    have h4_36_sq : 4 * (36 : ℝ) ^ t = (2 * (6 : ℝ) ^ t) ^ 2 := by
      rw [h36_sq]; ring
    have hlam_norm : Real.sqrt (∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2) ≤ (6 : ℝ) ^ t / Real.sqrt (n : ℝ) := by
      have h1 := (bpLam_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k).trans
        (div_le_div_of_nonneg_right hpow6 hn_pos.le)
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_div (by positivity), h36_sq, Real.sqrt_sq (by positivity)] at h2
      exact h2
    have hmu_norm : Real.sqrt (∑ v : Fin n, (bpMu lam γ σ ω ζ t k v) ^ 2) ≤ (6 : ℝ) ^ t / Real.sqrt (n : ℝ) := by
      have h1 := (bpMu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k).trans
        (div_le_div_of_nonneg_right hpow6 hn_pos.le)
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_div (by positivity), h36_sq, Real.sqrt_sq (by positivity)] at h2
      exact h2
    have hnu_norm : Real.sqrt (∑ v : Fin n, (bpNu lam γ σ ω ζ t k v) ^ 2) ≤ 2 * (6 : ℝ) ^ t / Real.sqrt (n : ℝ) := by
      have h1 := (bpNu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow6 (by norm_num)) hn_pos.le)
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_div (by positivity), h4_36_sq, Real.sqrt_sq (by positivity)] at h2
      exact h2
    have htA0 : |∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v| ≤
        (1 / (10 * Real.sqrt (n : ℝ))) *
          (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|) := by
      have hxt_a := abs_iterKick_lt_one hγ0 hγ1 hσ0 hσ ζ s x e.1.1 (abs_iterState_lt_one hlam ω ζ s e.1.1)
      have hxt_b := abs_iterKick_lt_one hγ0 hγ1 hσ0 hσ ζ s x e.1.2 (abs_iterState_lt_one hlam ω ζ s e.1.2)
      have hpw : ∀ v : Fin n, |bpMu lam γ σ ω ζ t k v * dA0 v| ≤
          (if v = e.1.1 then (1 / (10 * Real.sqrt (n : ℝ))) * |bpMu lam γ σ ω ζ t k e.1.1| else 0) +
          (if v = e.1.2 then (1 / (10 * Real.sqrt (n : ℝ))) * |bpMu lam γ σ ω ζ t k e.1.2| else 0) := by
        intro v
        rw [abs_mul]
        have hd0 : |dA0 v| ≤ (if v = e.1.1 then 1 / (10 * Real.sqrt (n : ℝ)) else 0) +
            (if v = e.1.2 then 1 / (10 * Real.sqrt (n : ℝ)) else 0) := by
          simp only [dA0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]
          have h1 := hgrad_diff_pt xt v
          have h2 : (if v = e.1.1 then 2 * |xt e.1.2| else 0) / Real.sqrt (n : ℝ) ≤
              (if v = e.1.1 then 2 / Real.sqrt (n : ℝ) else 0) := by
            split_ifs
            · exact div_le_div_of_nonneg_right (by linarith) hsq_pos.le
            · simp
          have h3 : (if v = e.1.2 then 2 * |xt e.1.1| else 0) / Real.sqrt (n : ℝ) ≤
              (if v = e.1.2 then 2 / Real.sqrt (n : ℝ) else 0) := by
            split_ifs
            · exact div_le_div_of_nonneg_right (by linarith) hsq_pos.le
            · simp
          have h4 : (1 / 20 : ℝ) * |iterGrad ω' xt v - iterGrad ω xt v| ≤
              (1 / 20 : ℝ) * ((if v = e.1.1 then 2 / Real.sqrt (n : ℝ) else 0) +
                (if v = e.1.2 then 2 / Real.sqrt (n : ℝ) else 0)) :=
            mul_le_mul_of_nonneg_left (h1.trans (add_le_add h2 h3)) (by norm_num)
          have hrw : (1 / 20 : ℝ) * ((if v = e.1.1 then 2 / Real.sqrt (n : ℝ) else 0) +
              (if v = e.1.2 then 2 / Real.sqrt (n : ℝ) else 0)) =
              (if v = e.1.1 then 1 / (10 * Real.sqrt (n : ℝ)) else 0) +
              (if v = e.1.2 then 1 / (10 * Real.sqrt (n : ℝ)) else 0) := by
            split_ifs <;> ring
          linarith [h4, hrw]
        have hmul := mul_le_mul_of_nonneg_left hd0 (abs_nonneg (bpMu lam γ σ ω ζ t k v))
        refine hmul.trans (le_of_eq ?_)
        by_cases h1 : v = e.1.1 <;> by_cases h2 : v = e.1.2
        · exact absurd (h1.symm.trans h2) e.2.ne
        · rw [h1]; simp [e.2.ne]; ring
        · rw [h2]; simp [e.2.ne.symm]; ring
        · simp [h1, h2]
      calc |∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v|
          ≤ ∑ v : Fin n, |bpMu lam γ σ ω ζ t k v * dA0 v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ v : Fin n,
              ((if v = e.1.1 then (1 / (10 * Real.sqrt (n : ℝ))) * |bpMu lam γ σ ω ζ t k e.1.1| else 0) +
               (if v = e.1.2 then (1 / (10 * Real.sqrt (n : ℝ))) * |bpMu lam γ σ ω ζ t k e.1.2| else 0)) :=
            Finset.sum_le_sum fun v _ => hpw v
        _ = (1 / (10 * Real.sqrt (n : ℝ))) *
              (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|) := by
            rw [Finset.sum_add_distrib]; simp [mul_add]
    have htA1 : |∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v| ≤
        (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have hdA1_sq : ∑ v : Fin n, (dA1 v) ^ 2 ≤ ((64 : ℝ) ^ t / (n : ℝ)) ^ 2 := by
        have h1 : ∑ v : Fin n, (dA1 v) ^ 2 = (1 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω' dxt v - iterGrad ω dxt v) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by simp only [dA1]; ring
        have h2 := hgrad_diff_sq dxt
        have hpair : (dxt e.1.1) ^ 2 + (dxt e.1.2) ^ 2 ≤ ∑ v : Fin n, (dxt v) ^ 2 := by
          have hsub : ({e.1.1, e.1.2} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
          have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun v => (dxt v) ^ 2) hsub fun _ _ _ => sq_nonneg _
          rwa [Finset.sum_pair e.2.ne] at hs
        have hdxt_sq : ∑ v : Fin n, (dxt v) ^ 2 ≤ 9 * ((64 : ℝ) ^ s / (n : ℝ)) := by
          have h3 : ∑ v : Fin n, (dxt v) ^ 2 ≤ 9 * ∑ v : Fin n, (dx v) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_le_sum fun v _ => ?_
            have hp := pow_le_pow_left₀ (abs_nonneg _) (hdxt_pw s v) 2
            rw [sq_abs, mul_pow, sq_abs] at hp
            linarith [hp, show (3 : ℝ) ^ 2 = 9 by norm_num]
          exact h3.trans (mul_le_mul_of_nonneg_left (hfwd s) (by norm_num))
        have hge1 : (1 : ℝ) ≤ (64 : ℝ) ^ t := one_le_pow₀ (by norm_num)
        have hsq_ge : (64 : ℝ) ^ s ≤ ((64 : ℝ) ^ t) ^ 2 := by nlinarith only [hpow64, hge1]
        rw [h1, div_pow]
        have hcomb : (1 / 400 : ℝ) * (4 * (9 * ((64 : ℝ) ^ s / (n : ℝ))) / (n : ℝ)) ≤
            ((64 : ℝ) ^ t) ^ 2 / (n : ℝ) ^ 2 := by
          have hrew : (1 / 400 : ℝ) * (4 * (9 * ((64 : ℝ) ^ s / (n : ℝ))) / (n : ℝ)) =
              (9 / 100 : ℝ) * (64 : ℝ) ^ s / (n : ℝ) ^ 2 := by ring
          rw [hrew]
          exact div_le_div_of_nonneg_right (by nlinarith only [hsq_ge, show (0 : ℝ) ≤ (64 : ℝ) ^ s by positivity]) (sq_nonneg _)
        have hstep1 : (1 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω' dxt v - iterGrad ω dxt v) ^ 2 ≤
            (1 / 400 : ℝ) * (4 * (9 * ((64 : ℝ) ^ s / (n : ℝ))) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (h2.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpair.trans hdxt_sq) (by norm_num)) hn_pos.le)) (by norm_num)
        exact hstep1.trans hcomb
      have hdA1_norm : Real.sqrt (∑ v : Fin n, (dA1 v) ^ 2) ≤ (64 : ℝ) ^ t / (n : ℝ) := by
        calc _ ≤ Real.sqrt (((64 : ℝ) ^ t / (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt hdA1_sq
          _ = (64 : ℝ) ^ t / (n : ℝ) := Real.sqrt_sq (by positivity)
      calc |∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v|
          ≤ Real.sqrt (∑ v : Fin n, (bpMu lam γ σ ω ζ t k v) ^ 2) *
              Real.sqrt (∑ v : Fin n, (dA1 v) ^ 2) := abs_sum_mul_le_sqrt_mul_sqrt _ _
        _ ≤ ((6 : ℝ) ^ t / Real.sqrt (n : ℝ)) * ((64 : ℝ) ^ t / (n : ℝ)) :=
            mul_le_mul hmu_norm hdA1_norm (Real.sqrt_nonneg _) (by positivity)
        _ = (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    have htr2 : |∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v| ≤
        (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have hr2_l1 : ∑ v : Fin n, |r2 v| ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by
        have hpw : ∀ v : Fin n, |r2 v| ≤ (50 / γ) * (dx v) ^ 2 := fun v => by
          simp only [r2, abs_mul, abs_of_nonneg hσ0]
          have htay := chi_taylor hγ0 hγ1 (x v) (dx v)
          have hadd : x v + dx v = x' v := by simp only [dx]; ring
          rw [hadd] at htay
          have h1 : σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v| ≤
              (25 / γ) * (dx v) ^ 2 := by
            calc σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v|
                ≤ (γ / 8) * ((200 / γ ^ 2) * (dx v) ^ 2) :=
                  mul_le_mul hσ htay (abs_nonneg _) (by positivity)
              _ = (25 / γ) * (dx v) ^ 2 := by field_simp; ring
          calc σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v| * |kickVal ζ s v|
              ≤ ((25 / γ) * (dx v) ^ 2) * 2 :=
                mul_le_mul h1 (abs_kickVal_lt_two ζ s v).le (abs_nonneg _) (by positivity)
            _ = (50 / γ) * (dx v) ^ 2 := by ring
        calc ∑ v : Fin n, |r2 v|
            ≤ ∑ v : Fin n, (50 / γ) * (dx v) ^ 2 := Finset.sum_le_sum fun v _ => hpw v
          _ = (50 / γ) * ∑ v : Fin n, (dx v) ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ (50 / γ) * ((64 : ℝ) ^ s / (n : ℝ)) := mul_le_mul_of_nonneg_left (hfwd s) (by positivity)
          _ ≤ (50 / γ) * ((64 : ℝ) ^ t / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow64 hn_pos.le) (by positivity)
          _ = (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by ring
      have hr2_norm : Real.sqrt (∑ v : Fin n, (r2 v) ^ 2) ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by
        calc _ ≤ Real.sqrt ((∑ v : Fin n, |r2 v|) ^ 2) := Real.sqrt_le_sqrt (sum_sq_le_sq_sum_abs r2)
          _ = ∑ v : Fin n, |r2 v| := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          _ ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := hr2_l1
      calc |∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v|
          ≤ Real.sqrt (∑ v : Fin n, (bpNu lam γ σ ω ζ t k v) ^ 2) *
              Real.sqrt (∑ v : Fin n, (r2 v) ^ 2) := abs_sum_mul_le_sqrt_mul_sqrt _ _
        _ ≤ (2 * (6 : ℝ) ^ t / Real.sqrt (n : ℝ)) * ((50 / γ) * (64 : ℝ) ^ t / (n : ℝ)) :=
            mul_le_mul hnu_norm hr2_norm (Real.sqrt_nonneg _) (by positivity)
        _ = (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    have htr1 : |∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v| ≤
        (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have hdu_sq : ∑ v : Fin n, (du v) ^ 2 ≤ (64 : ℝ) ^ t / (n : ℝ) := by
        have h1 := hdu_from_dx s
        have h2 := hfwd s
        have hpow_ge : (1 : ℝ) ≤ (64 : ℝ) ^ s := one_le_pow₀ (by norm_num)
        have h1n : 1 / (n : ℝ) ≤ (64 : ℝ) ^ s / (n : ℝ) :=
          div_le_div_of_nonneg_right hpow_ge hn_pos.le
        have h64 : (64 : ℝ) ^ (s + 1) / (n : ℝ) = 64 * ((64 : ℝ) ^ s / (n : ℝ)) := by
          rw [pow_succ']; ring
        have hnn : 0 ≤ (64 : ℝ) ^ s / (n : ℝ) := by positivity
        have h3 : ∑ v : Fin n, (du v) ^ 2 ≤ (64 : ℝ) ^ (s + 1) / (n : ℝ) := by
          linarith [h1, h2, h1n, h64, hnn]
        exact h3.trans (div_le_div_of_nonneg_right hpow64_s1 hn_pos.le)
      have hr1_l1 : ∑ v : Fin n, |r1 v| ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by
        have hpw : ∀ v : Fin n, |r1 v| ≤ (1 / Real.sqrt lam) * (du v) ^ 2 := fun v => by
          have htay := psi_taylor hlam (u v) (du v)
          have hadd : u v + du v = u' v := by simp only [du]; ring
          rw [hadd] at htay
          exact htay
        calc ∑ v : Fin n, |r1 v|
            ≤ ∑ v : Fin n, (1 / Real.sqrt lam) * (du v) ^ 2 := Finset.sum_le_sum fun v _ => hpw v
          _ = (1 / Real.sqrt lam) * ∑ v : Fin n, (du v) ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ (1 / Real.sqrt lam) * ((64 : ℝ) ^ t / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hdu_sq (by positivity)
          _ = (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by ring
      have hr1_norm : Real.sqrt (∑ v : Fin n, (r1 v) ^ 2) ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by
        calc _ ≤ Real.sqrt ((∑ v : Fin n, |r1 v|) ^ 2) := Real.sqrt_le_sqrt (sum_sq_le_sq_sum_abs r1)
          _ = ∑ v : Fin n, |r1 v| := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          _ ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := hr1_l1
      calc |∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v|
          ≤ Real.sqrt (∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2) *
              Real.sqrt (∑ v : Fin n, (r1 v) ^ 2) := abs_sum_mul_le_sqrt_mul_sqrt _ _
        _ ≤ ((6 : ℝ) ^ t / Real.sqrt (n : ℝ)) * ((1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ)) :=
            mul_le_mul hlam_norm hr1_norm (Real.sqrt_nonneg _) (by positivity)
        _ = (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    have htri1 := abs_add_le
      ((∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v) +
        (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v))
      (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v)
    have htri2 := abs_add_le
      ((∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v) +
        (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v))
      (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v)
    have htri3 := abs_add_le
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA0 v)
      (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * dA1 v)
    have hcomb_eq : (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) +
        (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) +
        (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) =
        (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
          ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    linarith [htri1, htri2, htri3, htA0, htA1, htr2, htr1, hcomb_eq]
  calc |F ω' - F ω|
      = |∑ k ∈ Finset.range t, (g k - g (k + 1))| := by rw [htele]
    _ ≤ ∑ k ∈ Finset.range t, |g k - g (k + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range t,
          ((1 / (10 * Real.sqrt (n : ℝ))) *
            (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|) +
          (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
            ((n : ℝ) * Real.sqrt (n : ℝ))) := Finset.sum_le_sum hstep_bd
    _ = (1 / (10 * Real.sqrt (n : ℝ))) *
          (∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|)) +
        C_rem / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          simp only [C_rem]; ring

/-- Sum of squared edge-flip differences on the good operator-norm event is `O(1 / n)`. -/
lemma edge_flip_diff_sq_sum_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t : ℕ) :
    let F : (EdgeIdx n → Bool) → ℝ := fun ω' => (∑ v : Fin n, iterState lam γ σ ω' ζ t v) / (n : ℝ)
    let C_rem : ℝ := (t : ℝ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t *
      (1 + 100 / γ + 1 / Real.sqrt lam)
    ∑ e : EdgeIdx n, (F (Function.update ω e (!ω e)) - F ω) ^ 2 ≤
      ((t : ℝ) ^ 2 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ) := by
  intro F C_rem
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsingle := fun e => edge_flip_single_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t e
  -- Square `hsingle e` and sum over `e : EdgeIdx n`.
  have hsq_e : ∀ e : EdgeIdx n,
      (F (Function.update ω e (!ω e)) - F ω) ^ 2 ≤
        ((t : ℝ) / (25 * (n : ℝ))) *
          (∑ k ∈ Finset.range t, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2)) +
        2 * C_rem ^ 2 / (n : ℝ) ^ 3 := by
    intro e
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hsingle e) 2
    rw [sq_abs] at h1
    set A := (1 / (10 * Real.sqrt (n : ℝ))) *
      (∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|))
    set B := C_rem / ((n : ℝ) * Real.sqrt (n : ℝ))
    have hAB : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
    have hA_sq : 2 * A ^ 2 ≤ ((t : ℝ) / (25 * (n : ℝ))) *
        (∑ k ∈ Finset.range t, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2)) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range t) (fun _ => (1 : ℝ))
        (fun k => |bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
      have h2sq : ∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|) ^ 2 ≤
          2 * ∑ k ∈ Finset.range t, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := sq_nonneg (|bpMu lam γ σ ω ζ t k e.1.1| - |bpMu lam γ σ ω ζ t k e.1.2|)
        nlinarith only [h1, sq_abs (bpMu lam γ σ ω ζ t k e.1.1), sq_abs (bpMu lam γ σ ω ζ t k e.1.2)]
      have hA_eq : 2 * A ^ 2 = (1 / (50 * (n : ℝ))) *
          (∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|)) ^ 2 := by
        simp only [A, mul_pow, div_pow, one_pow, Real.sq_sqrt hn_pos.le]; ring
      rw [hA_eq]
      have hcomb := hcs.trans (mul_le_mul_of_nonneg_left h2sq (Nat.cast_nonneg t))
      calc (1 / (50 * (n : ℝ))) *
            (∑ k ∈ Finset.range t, (|bpMu lam γ σ ω ζ t k e.1.1| + |bpMu lam γ σ ω ζ t k e.1.2|)) ^ 2
          ≤ (1 / (50 * (n : ℝ))) * ((t : ℝ) * (2 * ∑ k ∈ Finset.range t,
              ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2))) :=
            mul_le_mul_of_nonneg_left hcomb (by positivity)
        _ = ((t : ℝ) / (25 * (n : ℝ))) * ∑ k ∈ Finset.range t,
              ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2) := by ring
    have hB_sq : 2 * B ^ 2 = 2 * C_rem ^ 2 / (n : ℝ) ^ 3 := by
      simp only [B, div_pow, mul_pow, Real.sq_sqrt hn_pos.le]; ring
    linarith [h1, hAB, hA_sq, hB_sq]
  have hedge_sum_mu : ∀ k ∈ Finset.range t,
      ∑ e : EdgeIdx n, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2) ≤
        (36 : ℝ) ^ t := by
    intro k hk
    let f : Fin n × Fin n → ℝ := fun p => (bpMu lam γ σ ω ζ t k p.1) ^ 2
    have hlt : ∑ e : EdgeIdx n, (bpMu lam γ σ ω ζ t k e.1.1) ^ 2 =
        ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), f p := by
      refine Finset.sum_bij (fun e _ => e.1) ?_ ?_ ?_ ?_
      · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro p hp; exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
      · intro _ _; rfl
    have hgt : ∑ e : EdgeIdx n, (bpMu lam γ σ ω ζ t k e.1.2) ^ 2 =
        ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), f p := by
      refine Finset.sum_bij (fun e _ => (e.1.2, e.1.1)) ?_ ?_ ?_ ?_
      · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
      · intro e₁ _ e₂ _ h; simp only [Prod.mk.injEq] at h; exact Subtype.ext (Prod.ext h.2 h.1)
      · intro p hp; exact ⟨⟨(p.2, p.1), (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
      · intro _ _; rfl
    have hdisj : Disjoint (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
        (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hle_univ : ∑ e : EdgeIdx n, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2) ≤
        (n : ℝ) * ∑ v : Fin n, (bpMu lam γ σ ω ζ t k v) ^ 2 := by
      rw [Finset.sum_add_distrib, hlt, hgt, ← Finset.sum_union hdisj]
      calc ∑ p ∈ _ ∪ _, f p ≤ ∑ p : Fin n × Fin n, f p :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
        _ = ∑ v : Fin n, ∑ _w : Fin n, (bpMu lam γ σ ω ζ t k v) ^ 2 := by
            rw [Fintype.sum_prod_type]
        _ = (n : ℝ) * ∑ v : Fin n, (bpMu lam γ σ ω ζ t k v) ^ 2 := by
            simp [Finset.mul_sum]
    have hnorm := bpMu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 36) (Finset.mem_range.mp hk).le
    calc _ ≤ (n : ℝ) * ((36 : ℝ) ^ k / (n : ℝ)) :=
          hle_univ.trans (mul_le_mul_of_nonneg_left hnorm hn_pos.le)
      _ = (36 : ℝ) ^ k := mul_div_cancel₀ _ hn_pos.ne'
      _ ≤ (36 : ℝ) ^ t := hpow
  have hcard_edge : (Fintype.card (EdgeIdx n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 : Fintype.card (EdgeIdx n) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have h2 : Fintype.card (Fin n × Fin n) = n * n := by simp
    rw [h2] at h1
    exact_mod_cast (by simpa [sq] using h1)
  calc ∑ e : EdgeIdx n, (F (Function.update ω e (!ω e)) - F ω) ^ 2
      ≤ ∑ e : EdgeIdx n,
          (((t : ℝ) / (25 * (n : ℝ))) *
            (∑ k ∈ Finset.range t, ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2)) +
          2 * C_rem ^ 2 / (n : ℝ) ^ 3) := Finset.sum_le_sum fun e _ => hsq_e e
    _ = ((t : ℝ) / (25 * (n : ℝ))) *
          (∑ k ∈ Finset.range t, ∑ e : EdgeIdx n,
            ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2)) +
        (Fintype.card (EdgeIdx n) : ℝ) * (2 * C_rem ^ 2 / (n : ℝ) ^ 3) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((t : ℝ) / (25 * (n : ℝ))) * ((t : ℝ) * (36 : ℝ) ^ t) +
        (n : ℝ) ^ 2 * (2 * C_rem ^ 2 / (n : ℝ) ^ 3) := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right hcard_edge (by positivity))
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ k ∈ Finset.range t, ∑ e : EdgeIdx n,
                ((bpMu lam γ σ ω ζ t k e.1.1) ^ 2 + (bpMu lam γ σ ω ζ t k e.1.2) ^ 2)
              ≤ ∑ _k ∈ Finset.range t, (36 : ℝ) ^ t := Finset.sum_le_sum hedge_sum_mu
            _ = (t : ℝ) * (36 : ℝ) ^ t := by simp
    _ ≤ ((t : ℝ) ^ 2 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ) := by
          have h1 : (n : ℝ) ^ 2 * (2 * C_rem ^ 2 / (n : ℝ) ^ 3) = 2 * C_rem ^ 2 / (n : ℝ) := by
            field_simp
          have h2 : ((t : ℝ) / (25 * (n : ℝ))) * ((t : ℝ) * (36 : ℝ) ^ t) ≤
              (t : ℝ) ^ 2 * (36 : ℝ) ^ t / (n : ℝ) := by
            have heq : ((t : ℝ) / (25 * (n : ℝ))) * ((t : ℝ) * (36 : ℝ) ^ t) =
                (1 / 25 : ℝ) * ((t : ℝ) ^ 2 * (36 : ℝ) ^ t / (n : ℝ)) := by ring
            rw [heq]
            have hnn : 0 ≤ (t : ℝ) ^ 2 * (36 : ℝ) ^ t / (n : ℝ) := by positivity
            linarith
          rw [h1, add_div]; linarith

/-- Flip a single kick bit `(s₀, w₀, j₀)` in `ζ : KickBits T n`. -/
def flipKickBit {T n : ℕ} (ζ : KickBits T n) (s₀ : Fin T) (w₀ j₀ : Fin n) : KickBits T n :=
  fun s w j => if s = s₀ ∧ w = w₀ ∧ j = j₀ then !(ζ s w j) else ζ s w j

/-- Sum of squared kick-bit-flip differences on the good operator-norm event is `O(1 / n)`. -/
lemma kick_flip_diff_sq_sum_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (ω : EdgeIdx n → Bool) (ζ : KickBits T n)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (t : ℕ) :
    let F : KickBits T n → ℝ := fun ζ' => (∑ v : Fin n, iterState lam γ σ ω ζ' t v) / (n : ℝ)
    let C_rem : ℝ := (t : ℝ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t *
      (1 + 100 / γ + 1 / Real.sqrt lam)
    ∑ p : Fin T × Fin n × Fin n,
        (F (flipKickBit ζ p.1 p.2.1 p.2.2) - F ζ) ^ 2 ≤
      ((t : ℝ) * (8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2)) / (n : ℝ) := by
  intro F C_rem
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsingle : ∀ (s₀ : Fin T) (w₀ j₀ : Fin n),
      (F (flipKickBit ζ s₀ w₀ j₀) - F ζ) ^ 2 ≤
        if hlt : s₀.val < t then
          (2 / (n : ℝ)) * (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2 +
            2 * C_rem ^ 2 / (n : ℝ) ^ 3
        else 0 := by
    intro s₀ w₀ j₀
    set ζ' := flipKickBit ζ s₀ w₀ j₀
    have hkick_eq_of_ne : ∀ (s : ℕ) (v : Fin n), (s ≠ s₀.val ∨ v ≠ w₀) →
        kickVal ζ' s v = kickVal ζ s v := by
      intro s v hne
      unfold kickVal
      split_ifs with hs
      · congr 2; refine Finset.sum_congr rfl fun j _ => ?_
        have hnot : ¬ (⟨s, hs⟩ = s₀ ∧ v = w₀ ∧ j = j₀) := by
          rintro ⟨h1, h2, _⟩
          rcases hne with hne1 | hne2
          · exact hne1 (congrArg Fin.val h1)
          · exact hne2 h2
        simp [ζ', flipKickBit, hnot]
      · rfl
    have hkick_diff_at : |kickVal ζ' s₀.val w₀ - kickVal ζ s₀.val w₀| ≤ 2 / Real.sqrt (n : ℝ) := by
      simp only [kickVal, dif_pos s₀.isLt]
      have hlip := tau_lip
        ((∑ j : Fin n, if ζ' s₀ w₀ j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))
        ((∑ j : Fin n, if ζ s₀ w₀ j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))
      refine hlip.trans ?_
      rw [← sub_div, abs_div, abs_of_pos hsq_pos, ← Finset.sum_sub_distrib]
      refine div_le_div_of_nonneg_right ?_ hsq_pos.le
      have hsum : ∑ j : Fin n, ((if ζ' s₀ w₀ j then (1 : ℝ) else -1) - (if ζ s₀ w₀ j then (1 : ℝ) else -1)) =
          (if !(ζ s₀ w₀ j₀) then (1 : ℝ) else -1) - (if ζ s₀ w₀ j₀ then (1 : ℝ) else -1) := by
        rw [Finset.sum_eq_single j₀]
        · simp [ζ', flipKickBit]
        · intro j _ hne; simp [ζ', flipKickBit, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      cases ζ s₀ w₀ j₀ <;> norm_num
    have hpre : ∀ s : ℕ, s ≤ s₀.val → iterState lam γ σ ω ζ' s = iterState lam γ σ ω ζ s := by
      intro s
      induction s with
      | zero => intro _; rfl
      | succ s ih =>
        intro hs
        have hprev := ih (by omega)
        funext v
        change iterStep lam γ σ ω ζ' s (iterState lam γ σ ω ζ' s) v =
          iterStep lam γ σ ω ζ s (iterState lam γ σ ω ζ s) v
        rw [hprev]
        have hkt : iterKick γ σ ζ' s (iterState lam γ σ ω ζ s) =
            iterKick γ σ ζ s (iterState lam γ σ ω ζ s) := by
          funext w; simp only [iterKick, hkick_eq_of_ne s w (Or.inl (by omega))]
        simp only [iterStep, hkt]
    by_cases hlt : s₀.val < t
    · rw [dif_pos hlt]
      -- Forward `ℓ_2` bounds for `s ≤ t`.
      have hdxt_sq_all : ∀ s : ℕ,
          ∑ v : Fin n, (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s) v -
            iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v) ^ 2 ≤
          if s = s₀.val then 1 / (n : ℝ)
          else 9 * ∑ v : Fin n, (iterState lam γ σ ω ζ' s v - iterState lam γ σ ω ζ s v) ^ 2 := by
        intro s
        split_ifs with hss
        · subst hss
          rw [hpre s₀.val le_rfl]
          set x := iterState lam γ σ ω ζ s₀.val
          have hpw : ∀ v : Fin n, (iterKick γ σ ζ' s₀.val x v - iterKick γ σ ζ s₀.val x v) ^ 2 ≤
              if v = w₀ then 1 / (n : ℝ) else 0 := by
            intro v
            by_cases hvw : v = w₀
            · subst hvw
              rw [if_pos rfl]
              have hsub : iterKick γ σ ζ' s₀.val x v - iterKick γ σ ζ s₀.val x v =
                  σ * chi γ (x v) * (kickVal ζ' s₀.val v - kickVal ζ s₀.val v) := by
                simp only [iterKick]; ring
              have habs : |iterKick γ σ ζ' s₀.val x v - iterKick γ σ ζ s₀.val x v| ≤ 1 / Real.sqrt (n : ℝ) := by
                rw [hsub, abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (chi_bounds γ (x v)).1]
                have hσ_le : σ ≤ 1 / 2 := by linarith
                calc σ * chi γ (x v) * |kickVal ζ' s₀.val v - kickVal ζ s₀.val v|
                    ≤ (1 / 2) * 1 * (2 / Real.sqrt (n : ℝ)) :=
                      mul_le_mul (mul_le_mul hσ_le (chi_bounds γ (x v)).2 (chi_bounds γ (x v)).1 (by norm_num))
                        hkick_diff_at (abs_nonneg _) (by norm_num)
                  _ = 1 / Real.sqrt (n : ℝ) := by ring
              have h2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
              rwa [sq_abs, div_pow, one_pow, Real.sq_sqrt hn_pos.le] at h2
            · rw [if_neg hvw]
              simp [iterKick, hkick_eq_of_ne s₀.val v (Or.inr hvw)]
          calc ∑ v : Fin n, (iterKick γ σ ζ' s₀.val x v - iterKick γ σ ζ s₀.val x v) ^ 2
              ≤ ∑ v : Fin n, (if v = w₀ then 1 / (n : ℝ) else 0) := Finset.sum_le_sum fun v _ => hpw v
            _ = 1 / (n : ℝ) := by simp
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun v _ => ?_
          set x := iterState lam γ σ ω ζ s
          set x' := iterState lam γ σ ω ζ' s
          have heq : iterKick γ σ ζ' s x' v - iterKick γ σ ζ s x v =
              (x' v - x v) + σ * (chi γ (x' v) - chi γ (x v)) * kickVal ζ s v := by
            simp only [iterKick, hkick_eq_of_ne s v (Or.inl hss)]; ring
          have habs : |iterKick γ σ ζ' s x' v - iterKick γ σ ζ s x v| ≤ 3 * |x' v - x v| := by
            rw [heq]
            have h1 : |σ * (chi γ (x' v) - chi γ (x v)) * kickVal ζ s v| ≤ 2 * |x' v - x v| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
              have hc := chi_lip hγ0 hγ1 (x' v) (x v)
              have hsc : σ * |chi γ (x' v) - chi γ (x v)| ≤ |x' v - x v| := by
                calc σ * |chi γ (x' v) - chi γ (x v)|
                    ≤ (γ / 8) * ((8 / γ) * |x' v - x v|) :=
                      mul_le_mul hσ hc (abs_nonneg _) (by positivity)
                  _ = |x' v - x v| := by field_simp
              calc σ * |chi γ (x' v) - chi γ (x v)| * |kickVal ζ s v|
                  ≤ |x' v - x v| * 2 := mul_le_mul hsc (abs_kickVal_lt_two ζ s v).le (abs_nonneg _) (abs_nonneg _)
                _ = 2 * |x' v - x v| := mul_comm _ _
            exact (abs_add_le _ _).trans (by linarith)
          have h2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
          rw [sq_abs, mul_pow, sq_abs] at h2
          linarith [h2, show (3 : ℝ) ^ 2 = 9 by norm_num]
      have hdu_le_4dxt : ∀ s : ℕ,
          ∑ v : Fin n, ((iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s) v +
              (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s)) v) -
              (iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v +
              (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s (iterState lam γ σ ω ζ s)) v)) ^ 2 ≤
            4 * ∑ v : Fin n, (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s) v -
              iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v) ^ 2 := by
        intro s
        set xt := iterKick γ σ ζ s (iterState lam γ σ ω ζ s)
        set xt' := iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s)
        have hgrad := op_norm_matvec_sq hn ω (by norm_num : (0 : ℝ) ≤ 20) hop (fun v => xt' v - xt v)
        have hpw : ∑ v : Fin n, ((xt' v + (1 / 20 : ℝ) * iterGrad ω xt' v) -
              (xt v + (1 / 20 : ℝ) * iterGrad ω xt v)) ^ 2 ≤
            2 * ∑ v : Fin n, (xt' v - xt v) ^ 2 +
            (2 / 400 : ℝ) * ∑ v : Fin n, (iterGrad ω (fun w => xt' w - xt w) v) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun v _ => ?_
          have hlin : iterGrad ω xt' v - iterGrad ω xt v = iterGrad ω (fun w => xt' w - xt w) v := by
            simp only [iterGrad, ← sub_div, ← Finset.sum_sub_distrib]
            congr 1; refine Finset.sum_congr rfl fun w _ => by ring
          have hsub : (xt' v + (1 / 20 : ℝ) * iterGrad ω xt' v) -
              (xt v + (1 / 20 : ℝ) * iterGrad ω xt v) =
              (xt' v - xt v) + (1 / 20 : ℝ) * iterGrad ω (fun w => xt' w - xt w) v := by linarith [hlin]
          rw [hsub]
          nlinarith only [sq_nonneg ((xt' v - xt v) - (1 / 20 : ℝ) * iterGrad ω (fun w => xt' w - xt w) v)]
        linarith [hpw, hgrad]
      have hfwd : ∀ s : ℕ,
          ∑ v : Fin n, (iterState lam γ σ ω ζ' s v - iterState lam γ σ ω ζ s v) ^ 2 ≤
            (64 : ℝ) ^ s / (n : ℝ) := by
        intro s
        induction s with
        | zero => simp [iterState]
        | succ s ih =>
          have hlip_sum : ∑ v : Fin n,
              (iterState lam γ σ ω ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) ^ 2 ≤
              4 * ∑ v : Fin n, (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s) v -
                iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v) ^ 2 := by
            refine (Finset.sum_le_sum fun v _ => ?_).trans (hdu_le_4dxt s)
            have hl := psi_lip hlam
              (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s) v +
                (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ' s (iterState lam γ σ ω ζ' s)) v)
              (iterKick γ σ ζ s (iterState lam γ σ ω ζ s) v +
                (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ ζ s (iterState lam γ σ ω ζ s)) v)
            have h2 := pow_le_pow_left₀ (abs_nonneg _) hl 2
            rwa [sq_abs, sq_abs] at h2
          have hdxt := hdxt_sq_all s
          have hpow_ge : (1 : ℝ) ≤ (64 : ℝ) ^ s := one_le_pow₀ (by norm_num)
          have h64 : (64 : ℝ) ^ (s + 1) / (n : ℝ) = 64 * ((64 : ℝ) ^ s / (n : ℝ)) := by
            rw [pow_succ']; ring
          have hnn : 0 ≤ (64 : ℝ) ^ s / (n : ℝ) := by positivity
          split_ifs at hdxt
          · have h1n : 1 / (n : ℝ) ≤ (64 : ℝ) ^ s / (n : ℝ) :=
              div_le_div_of_nonneg_right hpow_ge hn_pos.le
            linarith [hlip_sum, hdxt, h1n, h64, hnn]
          · linarith [hlip_sum, hdxt, ih, h64, hnn]
      -- Telescope `g k - g (k + 1)` over `k ∈ Finset.range t`.
      let g : ℕ → ℝ := fun k =>
        ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
          (iterState lam γ σ ω ζ' (t - k) v - iterState lam γ σ ω ζ (t - k) v)
      have hg0 : g 0 = F ζ' - F ζ := by
        simp only [g, bpLam, Nat.sub_zero, F, one_div_mul_eq_div, ← Finset.sum_div,
          Finset.sum_sub_distrib, sub_div]
      have hgt : g t = 0 := by simp [g, iterState]
      have htele : F ζ' - F ζ = ∑ k ∈ Finset.range t, (g k - g (k + 1)) := by
        have h1 := Finset.sum_range_sub' g t
        linarith [h1, hg0, hgt]
      have hstep_bd : ∀ k ∈ Finset.range t,
          |g k - g (k + 1)| ≤
            (if k = t - 1 - s₀.val then (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| else 0) +
            (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
              ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        intro k hk
        have hklt : k < t := Finset.mem_range.mp hk
        set s := t - (k + 1)
        have hs1 : s + 1 = t - k := by omega
        have hst : s < t := by omega
        have hgk_eq : g k - g (k + 1) =
            ∑ v : Fin n, bpLam lam γ σ ω ζ t k v *
              (iterState lam γ σ ω ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
            ∑ v : Fin n, bpLam lam γ σ ω ζ t (k + 1) v *
              (iterState lam γ σ ω ζ' s v - iterState lam γ σ ω ζ s v) := by
          simp only [g, s, hs1]
        rw [hgk_eq, backprop_step_identity lam γ σ ω ω ζ ζ' t k hklt]
        set x := iterState lam γ σ ω ζ s
        set x' := iterState lam γ σ ω ζ' s
        set dx := fun v => x' v - x v
        set xt := iterKick γ σ ζ s x
        set xt' := iterKick γ σ ζ' s x'
        set u := fun v => xt v + (1 / 20 : ℝ) * iterGrad ω xt v
        set u' := fun v => xt' v + (1 / 20 : ℝ) * iterGrad ω xt' v
        set du := fun v => u' v - u v
        set r1 := fun v => (iterState lam γ σ ω ζ' (s + 1) v - iterState lam γ σ ω ζ (s + 1) v) -
          psiDeriv lam (u v) * du v
        set r2 := fun v => σ * (chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v) * kickVal ζ s v
        set dW0 := fun v => σ * chi γ (x v) * (kickVal ζ' s v - kickVal ζ s v)
        have hdW1 : ∀ v, σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ' s v - kickVal ζ s v) = 0 := by
          intro v
          by_cases hss : s = s₀.val
          · have hx_eq : x' = x := hpre s (by omega)
            simp [hx_eq]
          · simp [hkick_eq_of_ne s v (Or.inl hss)]
        have hrhs_clean :
            (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * ((1 / 20 : ℝ) * (iterGrad ω xt v - iterGrad ω xt v))) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
            (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * ((1 / 20 : ℝ) * (iterGrad ω (fun w => xt' w - xt w) v - iterGrad ω (fun w => xt' w - xt w) v))) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v *
              (r2 v + σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ' s v - kickVal ζ s v))) +
            (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) =
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v) +
            (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v) := by
          simp only [sub_self, mul_zero, Finset.sum_const_zero, zero_add, add_zero, hdW1]
        change |((∑ v : Fin n, bpMu lam γ σ ω ζ t k v * ((1 / 20 : ℝ) * (iterGrad ω xt v - iterGrad ω xt v))) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
            (∑ v : Fin n, bpMu lam γ σ ω ζ t k v * ((1 / 20 : ℝ) * (iterGrad ω (fun w => xt' w - xt w) v - iterGrad ω (fun w => xt' w - xt w) v))) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v *
              (r2 v + σ * (chi γ (x' v) - chi γ (x v)) * (kickVal ζ' s v - kickVal ζ s v))) +
            (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v))| ≤ _
        rw [hrhs_clean]
        have hpow6 : (36 : ℝ) ^ k ≤ (36 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hklt.le
        have hpow64 : (64 : ℝ) ^ s ≤ (64 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst.le
        have hpow64_s1 : (64 : ℝ) ^ (s + 1) ≤ (64 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst
        have h36_sq : (36 : ℝ) ^ t = ((6 : ℝ) ^ t) ^ 2 := by
          calc (36 : ℝ) ^ t = ((6 : ℝ) ^ 2) ^ t := by norm_num
            _ = ((6 : ℝ) ^ t) ^ 2 := by rw [← pow_mul, mul_comm 2 t, pow_mul]
        have h4_36_sq : 4 * (36 : ℝ) ^ t = (2 * (6 : ℝ) ^ t) ^ 2 := by rw [h36_sq]; ring
        have hlam_norm : Real.sqrt (∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2) ≤ (6 : ℝ) ^ t / Real.sqrt (n : ℝ) := by
          have h1 := (bpLam_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k).trans
            (div_le_div_of_nonneg_right hpow6 hn_pos.le)
          have h2 := Real.sqrt_le_sqrt h1
          rw [Real.sqrt_div (by positivity), h36_sq, Real.sqrt_sq (by positivity)] at h2
          exact h2
        have hnu_norm : Real.sqrt (∑ v : Fin n, (bpNu lam γ σ ω ζ t k v) ^ 2) ≤ 2 * (6 : ℝ) ^ t / Real.sqrt (n : ℝ) := by
          have h1 := (bpNu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t k).trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow6 (by norm_num)) hn_pos.le)
          have h2 := Real.sqrt_le_sqrt h1
          rw [Real.sqrt_div (by positivity), h4_36_sq, Real.sqrt_sq (by positivity)] at h2
          exact h2
        -- First-order term `|∑ ν * dW0|`.
        have htW0 : |∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v| ≤
            if k = t - 1 - s₀.val then (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| else 0 := by
          by_cases hk0 : k = t - 1 - s₀.val
          · rw [if_pos hk0]
            have hss : s = s₀.val := by omega
            have hsum : ∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v =
                bpNu lam γ σ ω ζ t k w₀ * dW0 w₀ := by
              rw [Finset.sum_eq_single w₀]
              · intro v _ hne; simp [dW0, hkick_eq_of_ne s v (Or.inr hne)]
              · intro h; exact absurd (Finset.mem_univ _) h
            rw [hsum, hk0, abs_mul]
            have hdW0_bd : |dW0 w₀| ≤ 1 / Real.sqrt (n : ℝ) := by
              simp only [dW0, hss, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (chi_bounds γ (x w₀)).1]
              have hσ_le : σ ≤ 1 / 2 := by linarith
              calc σ * chi γ (x w₀) * |kickVal ζ' s₀.val w₀ - kickVal ζ s₀.val w₀|
                  ≤ (1 / 2) * 1 * (2 / Real.sqrt (n : ℝ)) :=
                    mul_le_mul (mul_le_mul hσ_le (chi_bounds γ (x w₀)).2 (chi_bounds γ (x w₀)).1 (by norm_num))
                      hkick_diff_at (abs_nonneg _) (by norm_num)
                _ = 1 / Real.sqrt (n : ℝ) := by ring
            calc |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| * |dW0 w₀|
                ≤ |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| * (1 / Real.sqrt (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left hdW0_bd (abs_nonneg _)
              _ = (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| := mul_comm _ _
          · rw [if_neg hk0]
            have hss : s ≠ s₀.val := by omega
            have hzero : ∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v = 0 :=
              Finset.sum_eq_zero fun v _ => by simp [dW0, hkick_eq_of_ne s v (Or.inl hss)]
            rw [hzero, abs_zero]
        -- Remainder `r2`.
        have htr2 : |∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v| ≤
            (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
          have hr2_l1 : ∑ v : Fin n, |r2 v| ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by
            have hpw : ∀ v : Fin n, |r2 v| ≤ (50 / γ) * (dx v) ^ 2 := fun v => by
              simp only [r2, abs_mul, abs_of_nonneg hσ0]
              have htay := chi_taylor hγ0 hγ1 (x v) (dx v)
              have hadd : x v + dx v = x' v := by simp only [dx]; ring
              rw [hadd] at htay
              have h1 : σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v| ≤
                  (25 / γ) * (dx v) ^ 2 := by
                calc σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v|
                    ≤ (γ / 8) * ((200 / γ ^ 2) * (dx v) ^ 2) :=
                      mul_le_mul hσ htay (abs_nonneg _) (by positivity)
                  _ = (25 / γ) * (dx v) ^ 2 := by field_simp; ring
              calc σ * |chi γ (x' v) - chi γ (x v) - chiDeriv γ (x v) * dx v| * |kickVal ζ s v|
                  ≤ ((25 / γ) * (dx v) ^ 2) * 2 :=
                    mul_le_mul h1 (abs_kickVal_lt_two ζ s v).le (abs_nonneg _) (by positivity)
                _ = (50 / γ) * (dx v) ^ 2 := by ring
            calc ∑ v : Fin n, |r2 v|
                ≤ ∑ v : Fin n, (50 / γ) * (dx v) ^ 2 := Finset.sum_le_sum fun v _ => hpw v
              _ = (50 / γ) * ∑ v : Fin n, (dx v) ^ 2 := (Finset.mul_sum _ _ _).symm
              _ ≤ (50 / γ) * ((64 : ℝ) ^ s / (n : ℝ)) := mul_le_mul_of_nonneg_left (hfwd s) (by positivity)
              _ ≤ (50 / γ) * ((64 : ℝ) ^ t / (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow64 hn_pos.le) (by positivity)
              _ = (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by ring
          have hr2_norm : Real.sqrt (∑ v : Fin n, (r2 v) ^ 2) ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := by
            calc _ ≤ Real.sqrt ((∑ v : Fin n, |r2 v|) ^ 2) := Real.sqrt_le_sqrt (sum_sq_le_sq_sum_abs r2)
              _ = ∑ v : Fin n, |r2 v| := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)
              _ ≤ (50 / γ) * (64 : ℝ) ^ t / (n : ℝ) := hr2_l1
          calc |∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v|
              ≤ Real.sqrt (∑ v : Fin n, (bpNu lam γ σ ω ζ t k v) ^ 2) *
                  Real.sqrt (∑ v : Fin n, (r2 v) ^ 2) := abs_sum_mul_le_sqrt_mul_sqrt _ _
            _ ≤ (2 * (6 : ℝ) ^ t / Real.sqrt (n : ℝ)) * ((50 / γ) * (64 : ℝ) ^ t / (n : ℝ)) :=
                mul_le_mul hnu_norm hr2_norm (Real.sqrt_nonneg _) (by positivity)
            _ = (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        -- Remainder `r1`.
        have htr1 : |∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v| ≤
            (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
          have hdu_sq : ∑ v : Fin n, (du v) ^ 2 ≤ (64 : ℝ) ^ t / (n : ℝ) := by
            have h1 := hdu_le_4dxt s
            have hdxt := hdxt_sq_all s
            have hpow_ge : (1 : ℝ) ≤ (64 : ℝ) ^ s := one_le_pow₀ (by norm_num)
            have h64 : (64 : ℝ) ^ (s + 1) / (n : ℝ) = 64 * ((64 : ℝ) ^ s / (n : ℝ)) := by
              rw [pow_succ']; ring
            have hnn : 0 ≤ (64 : ℝ) ^ s / (n : ℝ) := by positivity
            have h3 : ∑ v : Fin n, (du v) ^ 2 ≤ (64 : ℝ) ^ (s + 1) / (n : ℝ) := by
              split_ifs at hdxt
              · have h1n : 1 / (n : ℝ) ≤ (64 : ℝ) ^ s / (n : ℝ) :=
                  div_le_div_of_nonneg_right hpow_ge hn_pos.le
                linarith [h1, hdxt, h1n, h64, hnn]
              · linarith [h1, hdxt, hfwd s, h64, hnn]
            exact h3.trans (div_le_div_of_nonneg_right hpow64_s1 hn_pos.le)
          have hr1_l1 : ∑ v : Fin n, |r1 v| ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by
            have hpw : ∀ v : Fin n, |r1 v| ≤ (1 / Real.sqrt lam) * (du v) ^ 2 := fun v => by
              have htay := psi_taylor hlam (u v) (du v)
              have hadd : u v + du v = u' v := by simp only [du]; ring
              rw [hadd] at htay
              exact htay
            calc ∑ v : Fin n, |r1 v|
                ≤ ∑ v : Fin n, (1 / Real.sqrt lam) * (du v) ^ 2 := Finset.sum_le_sum fun v _ => hpw v
              _ = (1 / Real.sqrt lam) * ∑ v : Fin n, (du v) ^ 2 := (Finset.mul_sum _ _ _).symm
              _ ≤ (1 / Real.sqrt lam) * ((64 : ℝ) ^ t / (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left hdu_sq (by positivity)
              _ = (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by ring
          have hr1_norm : Real.sqrt (∑ v : Fin n, (r1 v) ^ 2) ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := by
            calc _ ≤ Real.sqrt ((∑ v : Fin n, |r1 v|) ^ 2) := Real.sqrt_le_sqrt (sum_sq_le_sq_sum_abs r1)
              _ = ∑ v : Fin n, |r1 v| := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)
              _ ≤ (1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ) := hr1_l1
          calc |∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v|
              ≤ Real.sqrt (∑ v : Fin n, (bpLam lam γ σ ω ζ t k v) ^ 2) *
                  Real.sqrt (∑ v : Fin n, (r1 v) ^ 2) := abs_sum_mul_le_sqrt_mul_sqrt _ _
            _ ≤ ((6 : ℝ) ^ t / Real.sqrt (n : ℝ)) * ((1 / Real.sqrt lam) * (64 : ℝ) ^ t / (n : ℝ)) :=
                mul_le_mul hlam_norm hr1_norm (Real.sqrt_nonneg _) (by positivity)
            _ = (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        have htri1 := abs_add_le
          ((∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v) +
            (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v))
          (∑ v : Fin n, bpLam lam γ σ ω ζ t k v * r1 v)
        have htri2 := abs_add_le
          (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * dW0 v)
          (∑ v : Fin n, bpNu lam γ σ ω ζ t k v * r2 v)
        have hpos_ext : 0 ≤ (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) := by positivity
        have hcomb_eq : (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) +
            (100 / γ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) +
            (1 / Real.sqrt lam) * (6 : ℝ) ^ t * (64 : ℝ) ^ t / ((n : ℝ) * Real.sqrt (n : ℝ)) =
            (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
              ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        linarith [htri1, htri2, htW0, htr2, htr1, hpos_ext, hcomb_eq]
      have habs_diff : |F ζ' - F ζ| ≤
          (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| +
          C_rem / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        have hmem_k0 : t - 1 - s₀.val ∈ Finset.range t := Finset.mem_range.mpr (by omega)
        calc |F ζ' - F ζ|
            = |∑ k ∈ Finset.range t, (g k - g (k + 1))| := by rw [htele]
          _ ≤ ∑ k ∈ Finset.range t, |g k - g (k + 1)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range t,
                ((if k = t - 1 - s₀.val then (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| else 0) +
                (6 : ℝ) ^ t * (64 : ℝ) ^ t * (1 + 100 / γ + 1 / Real.sqrt lam) /
                  ((n : ℝ) * Real.sqrt (n : ℝ))) := Finset.sum_le_sum hstep_bd
          _ = (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀| +
              C_rem / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
                rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range t) (t - 1 - s₀.val),
                  if_pos hmem_k0, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                simp only [C_rem]; ring
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs_diff 2
      rw [sq_abs] at hsq
      set A := (1 / Real.sqrt (n : ℝ)) * |bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀|
      set B := C_rem / ((n : ℝ) * Real.sqrt (n : ℝ))
      have hAB : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
      have hA_eq : 2 * A ^ 2 = (2 / (n : ℝ)) * (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2 := by
        simp only [A, mul_pow, div_pow, one_pow, sq_abs, Real.sq_sqrt hn_pos.le]; ring
      have hB_eq : 2 * B ^ 2 = 2 * C_rem ^ 2 / (n : ℝ) ^ 3 := by
        simp only [B, div_pow, mul_pow, Real.sq_sqrt hn_pos.le]; ring
      linarith [hsq, hAB, hA_eq, hB_eq]
    · rw [dif_neg hlt]
      have hsame : iterState lam γ σ ω ζ' t = iterState lam γ σ ω ζ t := hpre t (by omega)
      simp [F, hsame]
  -- Sum `hsingle` over `(s₀, w₀, j₀) : Fin T × Fin n × Fin n`.
  rw [Fintype.sum_prod_type]
  calc ∑ s₀ : Fin T, ∑ q : Fin n × Fin n, (F (flipKickBit ζ s₀ q.1 q.2) - F ζ) ^ 2
      ≤ ∑ s₀ : Fin T, ∑ q : Fin n × Fin n,
          (if s₀.val < t then
            (2 / (n : ℝ)) * (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) q.1) ^ 2 +
              2 * C_rem ^ 2 / (n : ℝ) ^ 3
          else 0) :=
        Finset.sum_le_sum fun s₀ _ => Finset.sum_le_sum fun ⟨w₀, j₀⟩ _ => hsingle s₀ w₀ j₀
    _ ≤ ∑ s₀ : Fin T,
          (if s₀.val < t then (8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ) else 0) := by
        refine Finset.sum_le_sum fun s₀ _ => ?_
        split_ifs with hlt
        · rw [Fintype.sum_prod_type]
          simp_rw [Finset.sum_add_distrib]
          have h1 : ∑ w₀ : Fin n, ∑ _j₀ : Fin n,
              (2 / (n : ℝ)) * (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2 ≤
              8 * (36 : ℝ) ^ t / (n : ℝ) := by
            have heq : ∑ w₀ : Fin n, ∑ _j₀ : Fin n,
                (2 / (n : ℝ)) * (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2 =
                2 * ∑ w₀ : Fin n, (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2 := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← Finset.mul_sum]
              have : (n : ℝ) * (2 / (n : ℝ)) = 2 := by field_simp
              rw [← mul_assoc, this]
            rw [heq]
            have hnu := bpNu_norm_sq_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t (t - 1 - s₀.val)
            have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 36) (by omega : t - 1 - s₀.val ≤ t)
            calc 2 * ∑ w₀ : Fin n, (bpNu lam γ σ ω ζ t (t - 1 - s₀.val) w₀) ^ 2
                ≤ 2 * (4 * (36 : ℝ) ^ (t - 1 - s₀.val) / (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left hnu zero_le_two
              _ ≤ 2 * (4 * (36 : ℝ) ^ t / (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hpow (by norm_num)) hn_pos.le) zero_le_two
              _ = 8 * (36 : ℝ) ^ t / (n : ℝ) := by ring
          have h2 : ∑ _w₀ : Fin n, ∑ _j₀ : Fin n, (2 * C_rem ^ 2 / (n : ℝ) ^ 3) =
              2 * C_rem ^ 2 / (n : ℝ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
          rw [h2, add_div]; linarith [h1]
        · simp
    _ ≤ ((t : ℝ) * (8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2)) / (n : ℝ) := by
        have hcnt : ((Finset.univ.filter (fun s₀ : Fin T => s₀.val < t)).card : ℝ) ≤ (t : ℝ) := by
          have hinj : (Finset.univ.filter (fun s₀ : Fin T => s₀.val < t)).card ≤ (Finset.range t).card := by
            refine Finset.card_le_card_of_injOn Fin.val ?_ ?_
            · intro s hs; exact Finset.mem_range.mpr (Finset.mem_filter.mp hs).2
            · intro a _ b _ h; exact Fin.ext h
          rw [Finset.card_range] at hinj
          exact_mod_cast hinj
        have hsum_eq : ∑ s₀ : Fin T,
            (if s₀.val < t then (8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ) else 0) =
            ((Finset.univ.filter (fun s₀ : Fin T => s₀.val < t)).card : ℝ) *
              ((8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [hsum_eq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hcnt (by positivity)

/-- Product-space Efron–Stein inequality on `(EdgeIdx n → Bool) × KickBits T n` for mean-zero functions. -/
lemma efron_stein_edge_kick {T n : ℕ} (F : (EdgeIdx n → Bool) × KickBits T n → ℝ)
    (hμ0 : ∑ p : (EdgeIdx n → Bool) × KickBits T n, F p = 0) :
    ∑ p : (EdgeIdx n → Bool) × KickBits T n, (F p) ^ 2 ≤
      (1 / 4 : ℝ) * ∑ p : (EdgeIdx n → Bool) × KickBits T n,
        ((∑ e : EdgeIdx n, (F (Function.update p.1 e (!p.1 e), p.2) - F p) ^ 2) +
         (∑ q : Fin T × Fin n × Fin n, (F (p.1, flipKickBit p.2 q.1 q.2.1 q.2.2) - F p) ^ 2)) := by
  let X := EdgeIdx n ⊕ (Fin T × Fin n × Fin n)
  let eProd : ((EdgeIdx n → Bool) × KickBits T n) ≃ (X → Bool) :=
    { toFun := fun p x => Sum.casesOn x p.1 (fun q => p.2 q.1 q.2.1 q.2.2)
      invFun := fun f => (fun e => f (Sum.inl e), fun s w j => f (Sum.inr (s, w, j)))
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun f => by funext x; rcases x with e | ⟨s, w, j⟩ <;> rfl }
  have hcard_eq : (Fintype.card (X → Bool) : ℝ) =
      (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) := by
    exact_mod_cast (Fintype.card_congr eProd).symm
  have hcard_pos : (0 : ℝ) < (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hes := efron_stein_bool (X := X) (fun f => F (eProd.symm f))
  have hμ0' : (∑ f : X → Bool, F (eProd.symm f)) / (Fintype.card (X → Bool) : ℝ) = 0 := by
    rw [Equiv.sum_comp eProd.symm F, hμ0, zero_div]
  simp only [hμ0', sub_zero] at hes
  have hL : ∑ f : X → Bool, (F (eProd.symm f)) ^ 2 =
      ∑ p : (EdgeIdx n → Bool) × KickBits T n, (F p) ^ 2 :=
    Equiv.sum_comp eProd.symm (fun p => (F p) ^ 2)
  have hR : ∑ x : X, ∑ f : X → Bool, (F (eProd.symm f) - F (eProd.symm (Function.update f x (!f x)))) ^ 2 =
      ∑ p : (EdgeIdx n → Bool) × KickBits T n,
        ((∑ e : EdgeIdx n, (F (Function.update p.1 e (!p.1 e), p.2) - F p) ^ 2) +
         (∑ q : Fin T × Fin n × Fin n, (F (p.1, flipKickBit p.2 q.1 q.2.1 q.2.2) - F p) ^ 2)) := by
    rw [Finset.sum_comm]
    rw [← Equiv.sum_comp eProd (fun f => ∑ x : X,
      (F (eProd.symm f) - F (eProd.symm (Function.update f x (!f x)))) ^ 2)]
    refine Finset.sum_congr rfl fun ⟨ω, ζ⟩ _ => ?_
    rw [Fintype.sum_sum_type]
    congr 1
    · refine Finset.sum_congr rfl fun e _ => ?_
      have h1 : eProd.symm (eProd (ω, ζ)) = (ω, ζ) := eProd.left_inv (ω, ζ)
      have h2 : eProd.symm (Function.update (eProd (ω, ζ)) (Sum.inl e) (!eProd (ω, ζ) (Sum.inl e))) =
          (Function.update ω e (!ω e), ζ) := by
        apply Prod.ext
        · funext e'
          by_cases h : e' = e
          · subst h; simp [eProd]
          · simp [eProd, Function.update_of_ne (Sum.inl_injective.ne h), Function.update_of_ne h]
        · funext s w j; simp [eProd]
      rw [h1, h2]; ring
    · refine Finset.sum_congr rfl fun ⟨s₀, w₀, j₀⟩ _ => ?_
      have h1 : eProd.symm (eProd (ω, ζ)) = (ω, ζ) := eProd.left_inv (ω, ζ)
      have h2 : eProd.symm (Function.update (eProd (ω, ζ)) (Sum.inr (s₀, w₀, j₀))
            (!eProd (ω, ζ) (Sum.inr (s₀, w₀, j₀)))) =
          (ω, flipKickBit ζ s₀ w₀ j₀) := by
        apply Prod.ext
        · funext e'; simp [eProd]
        · funext s w j
          simp only [eProd, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, flipKickBit]
          by_cases h : (s, w, j) = (s₀, w₀, j₀)
          · rcases Prod.mk.inj h with ⟨rfl, h2⟩
            rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
            simp
          · have hnot : ¬ (s = s₀ ∧ w = w₀ ∧ j = j₀) := by
              rintro ⟨rfl, rfl, rfl⟩; exact h rfl
            simp [Function.update_of_ne (Sum.inr_injective.ne h), hnot]
      rw [h1, h2]; ring
  rw [← Finset.sum_div, hL, hR, hcard_eq, div_le_iff₀ hcard_pos] at hes
  rw [mul_assoc, div_mul_cancel₀ _ hcard_pos.ne'] at hes
  exact hes

/-- Global Efron–Stein variance bound for `(1 / n) ∑_v x_t(v)` over uniform `(ω, ζ)`. -/
theorem mean_iterState_var_le {T n : ℕ} (hn : 1 ≤ n) {lam γ σ : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8) (t : ℕ) :
    let F : (EdgeIdx n → Bool) × KickBits T n → ℝ :=
      fun p => (∑ v : Fin n, iterState lam γ σ p.1 p.2 t v) / (n : ℝ)
    let C_rem : ℝ := (t : ℝ) * (6 : ℝ) ^ t * (64 : ℝ) ^ t *
      (1 + 100 / γ + 1 / Real.sqrt lam)
    let C_var : ℝ := ((t : ℝ) ^ 2 + 8 * (t : ℝ)) * (36 : ℝ) ^ t + 2 * ((t : ℝ) + 1) * C_rem ^ 2
    ∑ p : (EdgeIdx n → Bool) × KickBits T n, (F p) ^ 2 ≤
      (C_var / (n : ℝ) + 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ))) *
        (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) := by
  intro F C_rem C_var
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcard_pos : (0 : ℝ) < (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hes := efron_stein_edge_kick F (avg_mean_iterState_eq_zero lam γ σ t)
  have hC_nn : 0 ≤ C_var / (n : ℝ) :=
    div_nonneg (add_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg (by positivity) (sq_nonneg C_rem))) hn_pos.le
  -- Bound the inner sum for `ω ∈ GoodOp` and `ω ∉ GoodOp`.
  let BadOp : Finset (EdgeIdx n → Bool) := Finset.univ.filter (fun ω : EdgeIdx n → Bool =>
    ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
      20 * Real.sqrt (n : ℝ) < |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|)
  have hF_bd : ∀ p : (EdgeIdx n → Bool) × KickBits T n, |F p| ≤ 1 := by
    intro ⟨ω, ζ⟩
    simp only [F, abs_div, abs_of_pos hn_pos, div_le_one hn_pos]
    calc |∑ v : Fin n, iterState lam γ σ ω ζ t v|
        ≤ ∑ v : Fin n, |iterState lam γ σ ω ζ t v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n, (1 : ℝ) := Finset.sum_le_sum fun v _ => (abs_iterState_lt_one hlam ω ζ t v).le
      _ = (n : ℝ) := by simp
  have hcard_edge : (Fintype.card (EdgeIdx n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 : Fintype.card (EdgeIdx n) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have h2 : Fintype.card (Fin n × Fin n) = n * n := by simp
    rw [h2] at h1
    exact_mod_cast (by simpa [sq] using h1)
  have hpw : ∀ p : (EdgeIdx n → Bool) × KickBits T n,
      (∑ e : EdgeIdx n, (F (Function.update p.1 e (!p.1 e), p.2) - F p) ^ 2) +
      (∑ q : Fin T × Fin n × Fin n, (F (p.1, flipKickBit p.2 q.1 q.2.1 q.2.2) - F p) ^ 2) ≤
      C_var / (n : ℝ) + if p.1 ∈ BadOp then 4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 else 0 := by
    intro ⟨ω, ζ⟩
    by_cases hbad : ω ∈ BadOp
    · rw [if_pos hbad]
      have h1 : ∑ e : EdgeIdx n, (F (Function.update ω e (!ω e), ζ) - F (ω, ζ)) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
        calc _ ≤ ∑ _e : EdgeIdx n, (4 : ℝ) := Finset.sum_le_sum fun e _ => by
              have ha := abs_le.mp (hF_bd (Function.update ω e (!ω e), ζ))
              have hb := abs_le.mp (hF_bd (ω, ζ))
              nlinarith only [ha.1, ha.2, hb.1, hb.2]
          _ = (Fintype.card (EdgeIdx n) : ℝ) * 4 := by simp
          _ ≤ (n : ℝ) ^ 2 * 4 := mul_le_mul_of_nonneg_right hcard_edge (by norm_num)
          _ = 4 * (n : ℝ) ^ 2 := mul_comm _ _
      have h2 : ∑ q : Fin T × Fin n × Fin n,
          (F (ω, flipKickBit ζ q.1 q.2.1 q.2.2) - F (ω, ζ)) ^ 2 ≤ 4 * (T : ℝ) * (n : ℝ) ^ 2 := by
        calc _ ≤ ∑ _q : Fin T × Fin n × Fin n, (4 : ℝ) := Finset.sum_le_sum fun q _ => by
              have ha := abs_le.mp (hF_bd (ω, flipKickBit ζ q.1 q.2.1 q.2.2))
              have hb := abs_le.mp (hF_bd (ω, ζ))
              nlinarith only [ha.1, ha.2, hb.1, hb.2]
          _ = (Fintype.card (Fin T × Fin n × Fin n) : ℝ) * 4 := by simp
          _ = 4 * (T : ℝ) * (n : ℝ) ^ 2 := by simp [sq]; ring
      linarith only [h1, h2, hC_nn]
    · rw [if_neg hbad, add_zero]
      have hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
          |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ) := by
        intro x y hx hy
        by_contra hgt
        exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, y, hx, hy, lt_of_not_ge hgt⟩⟩)
      have he := edge_flip_diff_sq_sum_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t
      have hk := kick_flip_diff_sq_sum_le hn hlam hγ0 hγ1 hσ0 hσ ω ζ hop t
      have hsum_eq : ((t : ℝ) ^ 2 * (36 : ℝ) ^ t + 2 * C_rem ^ 2) / (n : ℝ) +
          ((t : ℝ) * (8 * (36 : ℝ) ^ t + 2 * C_rem ^ 2)) / (n : ℝ) = C_var / (n : ℝ) := by
        simp only [C_var]; ring
      linarith only [he, hk, hsum_eq]
  have hbad_sum : ∑ p : (EdgeIdx n → Bool) × KickBits T n,
      (if p.1 ∈ BadOp then 4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 else 0) ≤
      8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) *
        (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ ω : EdgeIdx n → Bool,
        ∑ _ζ : KickBits T n, (if ω ∈ BadOp then 4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 else 0) =
        if ω ∈ BadOp then (Fintype.card (KickBits T n) : ℝ) * (4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2) else 0 := by
      intro ω; split_ifs <;> simp
    simp_rw [hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hfilt : Finset.univ.filter (fun ω : EdgeIdx n → Bool => ω ∈ BadOp) = BadOp := by
      ext ω; simp
    rw [hfilt]
    have hop_bad := op_norm_bad_bound hn
    have hprod_card : (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) =
        (Fintype.card (EdgeIdx n → Bool) : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
      simp
    rw [hprod_card]
    calc (BadOp.card : ℝ) * ((Fintype.card (KickBits T n) : ℝ) * (4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2))
        ≤ (2 * Real.exp (-2 * (n : ℝ)) * (Fintype.card (EdgeIdx n → Bool) : ℝ)) *
            ((Fintype.card (KickBits T n) : ℝ) * (4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hop_bad (by positivity)
      _ = 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) *
            ((Fintype.card (EdgeIdx n → Bool) : ℝ) * (Fintype.card (KickBits T n) : ℝ)) := by ring
  have hsum_R : ∑ p : (EdgeIdx n → Bool) × KickBits T n,
      ((∑ e : EdgeIdx n, (F (Function.update p.1 e (!p.1 e), p.2) - F p) ^ 2) +
       (∑ q : Fin T × Fin n × Fin n, (F (p.1, flipKickBit p.2 q.1 q.2.1 q.2.2) - F p) ^ 2)) ≤
      (C_var / (n : ℝ) + 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ))) *
        (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) := by
    calc _ ≤ ∑ p : (EdgeIdx n → Bool) × KickBits T n,
          (C_var / (n : ℝ) + if p.1 ∈ BadOp then 4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 else 0) :=
          Finset.sum_le_sum fun p _ => hpw p
      _ = (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) * (C_var / (n : ℝ)) +
          ∑ p : (EdgeIdx n → Bool) × KickBits T n,
            (if p.1 ∈ BadOp then 4 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) * (C_var / (n : ℝ)) +
          8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) *
            (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) :=
          add_le_add le_rfl hbad_sum
      _ = (C_var / (n : ℝ) + 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ))) *
            (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) := by ring
  have hR_nn : 0 ≤ (C_var / (n : ℝ) + 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ))) *
      (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) :=
    mul_nonneg (add_nonneg hC_nn (by positivity)) hcard_pos.le
  linarith only [hes, hsum_R, hR_nn]

end KickedProx


/- ### Section 5b: Paley–Zygmund Escape from Interior Vertices & Pointwise Energy Telescoping -/

section KickEscape

/-- Single-step kick value `W_1(ξ, v) = τ((1/√n) ∑_j ±1)` for one step's kick bits `ξ : Fin n → Fin n → Bool`. -/
noncomputable def stepKickVal {n : ℕ} (ξ : Fin n → Fin n → Bool) (v : Fin n) : ℝ :=
  tau ((∑ j : Fin n, if ξ v j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))

/-- Flip all `n` kick bits of a single vertex `a`. -/
def flipVertexBits {n : ℕ} (a : Fin n) (ξ : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun u j => if u = a then !(ξ u j) else ξ u j

lemma flipVertexBits_involutive {n : ℕ} (a : Fin n) (ξ : Fin n → Fin n → Bool) :
    flipVertexBits a (flipVertexBits a ξ) = ξ := by
  funext u j; by_cases h : u = a <;> simp [flipVertexBits, h]

lemma stepKickVal_flipVertexBits {n : ℕ} (a v : Fin n) (ξ : Fin n → Fin n → Bool) :
    stepKickVal (flipVertexBits a ξ) v = if v = a then -stepKickVal ξ v else stepKickVal ξ v := by
  by_cases h : v = a
  · subst h
    simp only [stepKickVal, flipVertexBits, ite_true]
    have hsum : (∑ j : Fin n, if !(ξ v j) then (1 : ℝ) else -1) =
        -(∑ j : Fin n, if ξ v j then (1 : ℝ) else -1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => by cases ξ v j <;> norm_num
    rw [hsum, neg_div, tau_neg]
  · simp [stepKickVal, flipVertexBits, h]

lemma sum_stepKick_flip_zero {n : ℕ} (a : Fin n) (g : (Fin n → Fin n → Bool) → ℝ)
    (hg : ∀ ξ, g (flipVertexBits a ξ) = -g ξ) :
    ∑ ξ : Fin n → Fin n → Bool, g ξ = 0 := by
  let inv : (Fin n → Fin n → Bool) ≃ (Fin n → Fin n → Bool) :=
    ⟨flipVertexBits a, flipVertexBits a, flipVertexBits_involutive a, flipVertexBits_involutive a⟩
  have h1 : ∑ ξ : Fin n → Fin n → Bool, g ξ = ∑ ξ : Fin n → Fin n → Bool, -g ξ := by
    calc _ = ∑ ξ, g (inv ξ) := (Equiv.sum_comp inv g).symm
      _ = ∑ ξ, -g ξ := Finset.sum_congr rfl fun ξ _ => hg ξ
  rw [Finset.sum_neg_distrib] at h1
  linarith

lemma abs_stepKickVal_lt_two {n : ℕ} (ξ : Fin n → Fin n → Bool) (v : Fin n) :
    |stepKickVal ξ v| < 2 := abs_tau_lt_two _

lemma sum_stepKickVal_sq_ge {n : ℕ} (hn : 1 ≤ n) (v : Fin n) :
    (1 / 25 : ℝ) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) ≤
      ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ v) ^ 2 := by
  let e : (Fin n → Fin n → Bool) ≃ (Fin n → Bool) × ({u : Fin n // u ≠ v} → Fin n → Bool) :=
    { toFun := fun ξ => (ξ v, fun u => ξ u.1)
      invFun := fun p u => if h : u = v then p.1 else p.2 ⟨u, h⟩
      left_inv := fun ξ => by funext u j; by_cases h : u = v <;> simp [h]
      right_inv := fun ⟨a, b⟩ => by
        apply Prod.ext
        · funext j; simp
        · funext u j; simp [u.2] }
  have hsum : ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ v) ^ 2 =
      (Fintype.card ({u : Fin n // u ≠ v} → Fin n → Bool) : ℝ) *
        ∑ a : Fin n → Bool,
          (tau ((∑ j : Fin n, if a j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))) ^ 2 := by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    have hconst : ∀ a : Fin n → Bool,
        ∑ _b : {u : Fin n // u ≠ v} → Fin n → Bool, (stepKickVal (e.symm (a, _b)) v) ^ 2 =
        (Fintype.card ({u : Fin n // u ≠ v} → Fin n → Bool) : ℝ) *
          (tau ((∑ j : Fin n, if a j then (1 : ℝ) else -1) / Real.sqrt (n : ℝ))) ^ 2 := by
      intro a
      simp [e, stepKickVal]
    simp_rw [hconst, ← Finset.mul_sum]
  have hcard : (Fintype.card (Fin n → Fin n → Bool) : ℝ) =
      (Fintype.card ({u : Fin n // u ≠ v} → Fin n → Bool) : ℝ) *
        (Fintype.card (Fin n → Bool) : ℝ) := by
    have h1 := Fintype.card_congr e
    rw [Fintype.card_prod] at h1
    rw [h1, Nat.cast_mul, mul_comm]
  rw [hsum, hcard]
  have htau := tau_rademacher_second_moment hn
  calc (1 / 25 : ℝ) * ((Fintype.card ({u : Fin n // u ≠ v} → Fin n → Bool) : ℝ) *
          (Fintype.card (Fin n → Bool) : ℝ))
      = (Fintype.card ({u : Fin n // u ≠ v} → Fin n → Bool) : ℝ) *
          ((1 / 25 : ℝ) * (Fintype.card (Fin n → Bool) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htau (Nat.cast_nonneg _)

/-- Exact zero average of the quadratic energy change under a single kick step. -/
lemma kick_quad_avg_zero {n : ℕ} (ω : EdgeIdx n → Bool) (γ σ : ℝ) (x : Fin n → ℝ) :
    let xt : (Fin n → Fin n → Bool) → Fin n → ℝ :=
      fun ξ v => x v + σ * chi γ (x v) * stepKickVal ξ v
    ∑ ξ : Fin n → Fin n → Bool,
        (∑ i : Fin n, ∑ j : Fin n, xt ξ i * adjSign ω i j * xt ξ j) =
      (Fintype.card (Fin n → Fin n → Bool) : ℝ) *
        (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) := by
  intro xt
  have hswap : ∑ ξ : Fin n → Fin n → Bool,
      (∑ i : Fin n, ∑ j : Fin n, xt ξ i * adjSign ω i j * xt ξ j) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ ξ : Fin n → Fin n → Bool, xt ξ i * adjSign ω i j * xt ξ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : ∀ ξ, xt ξ i * adjSign ω i j * xt ξ j =
      x i * adjSign ω i j * x j +
      (x i * adjSign ω i j * (σ * chi γ (x j))) * stepKickVal ξ j +
      (σ * chi γ (x i) * adjSign ω i j * x j) * stepKickVal ξ i +
      (σ * chi γ (x i) * adjSign ω i j * (σ * chi γ (x j))) * (stepKickVal ξ i * stepKickVal ξ j) := by
    intro ξ; simp only [xt]; ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hz1 : ∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ j = 0 :=
    sum_stepKick_flip_zero j (fun ξ => stepKickVal ξ j) fun ξ => by
      simp [stepKickVal_flipVertexBits]
  have hz2 : ∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i = 0 :=
    sum_stepKick_flip_zero i (fun ξ => stepKickVal ξ i) fun ξ => by
      simp [stepKickVal_flipVertexBits]
  have hz3 : adjSign ω i j * (∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i * stepKickVal ξ j) = 0 := by
    by_cases hij : i = j
    · subst hij; simp [adjSign_diag]
    · have h0 : ∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i * stepKickVal ξ j = 0 :=
        sum_stepKick_flip_zero i (fun ξ => stepKickVal ξ i * stepKickVal ξ j) fun ξ => by
          rw [stepKickVal_flipVertexBits, stepKickVal_flipVertexBits, if_pos rfl, if_neg (Ne.symm hij)]
          ring
      rw [h0, mul_zero]
  have hterm3 : (σ * chi γ (x i) * adjSign ω i j * (σ * chi γ (x j))) *
      (∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i * stepKickVal ξ j) = 0 := by
    have : (σ * chi γ (x i) * adjSign ω i j * (σ * chi γ (x j))) *
        (∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i * stepKickVal ξ j) =
        (σ * chi γ (x i) * (σ * chi γ (x j))) *
        (adjSign ω i j * ∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ i * stepKickVal ξ j) := by ring
    rw [this, hz3, mul_zero]
  rw [hz1, hz2, mul_zero, mul_zero, add_zero, add_zero, hterm3, add_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]; ring

/-- Single-vertex Paley–Zygmund escape probability when at least `δ n` vertices are interior. -/
lemma kick_single_vertex_escape {n : ℕ} (hn : 1 ≤ n) (ω : EdgeIdx n → Bool)
    {γ σ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 < σ) (hδ0 : 0 < δ)
    (hnδ : 2 ≤ δ * (n : ℝ)) (x : Fin n → ℝ) (v : Fin n)
    (hI : δ * (n : ℝ) ≤ ((Finset.univ.filter (fun w : Fin n => |x w| ≤ 1 - γ)).card : ℝ)) :
    let xt : (Fin n → Fin n → Bool) → Fin n → ℝ :=
      fun ξ u => x u + σ * chi γ (x u) * stepKickVal ξ u
    (δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) ≤
      ((Finset.univ.filter (fun ξ : Fin n → Fin n → Bool =>
        σ * Real.sqrt (δ / 200) ≤ |iterGrad ω (xt ξ) v|)).card : ℝ) := by
  intro xt
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let c : Fin n → ℝ := fun w => adjSign ω v w * chi γ (x w)
  let Z0 : (Fin n → Fin n → Bool) → ℝ := fun ξ =>
    (∑ w : Fin n, c w * stepKickVal ξ w) / Real.sqrt (n : ℝ)
  set Nξ : ℝ := (Fintype.card (Fin n → Fin n → Bool) : ℝ)
  have hNξ_pos : 0 < Nξ := Nat.cast_pos.mpr Fintype.card_pos
  have hc_bd : ∀ w, |c w| ≤ 1 := fun w => by
    simp only [c, abs_mul]
    have ha : |adjSign ω v w| ≤ 1 := by unfold adjSign; split_ifs <;> norm_num
    have hb : |chi γ (x w)| ≤ 1 := by
      rw [abs_of_nonneg (chi_bounds γ (x w)).1]; exact (chi_bounds γ (x w)).2
    exact (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hgrad_split : ∀ ξ, iterGrad ω (xt ξ) v = iterGrad ω x v + σ * Z0 ξ := fun ξ => by
    simp only [iterGrad, xt, Z0, c, mul_div_assoc', ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl fun w _ => by ring
  -- Second moment lower bound: `∑ (Z0 ξ)^2 ≥ (δ / 50) * Nξ`.
  have hE2 : (δ / 50) * Nξ ≤ ∑ ξ : Fin n → Fin n → Bool, (Z0 ξ) ^ 2 := by
    have hexp : ∀ ξ, (Z0 ξ) ^ 2 =
        (∑ w₁ : Fin n, ∑ w₂ : Fin n, (c w₁ * c w₂) * (stepKickVal ξ w₁ * stepKickVal ξ w₂)) / (n : ℝ) := by
      intro ξ
      simp only [Z0]
      rw [div_pow, Real.sq_sqrt hn_pos.le, sq, Finset.sum_mul]
      congr 1; refine Finset.sum_congr rfl fun w₁ _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w₂ _ => by ring
    simp_rw [hexp]
    rw [← Finset.sum_div, Finset.sum_comm]
    have hdiag_only : ∑ w₁ : Fin n, ∑ ξ : Fin n → Fin n → Bool,
        ∑ w₂ : Fin n, (c w₁ * c w₂) * (stepKickVal ξ w₁ * stepKickVal ξ w₂) =
        ∑ w : Fin n, (c w) ^ 2 * ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ w) ^ 2 := by
      refine Finset.sum_congr rfl fun w₁ _ => ?_
      rw [Finset.sum_comm, Finset.sum_eq_single w₁]
      · simp_rw [← Finset.mul_sum, sq]
      · intro w₂ _ hne
        rw [← Finset.mul_sum]
        have hz : ∑ ξ : Fin n → Fin n → Bool, stepKickVal ξ w₁ * stepKickVal ξ w₂ = 0 :=
          sum_stepKick_flip_zero w₁ (fun ξ => stepKickVal ξ w₁ * stepKickVal ξ w₂) fun ξ => by
            rw [stepKickVal_flipVertexBits, stepKickVal_flipVertexBits, if_pos rfl, if_neg hne]; ring
        rw [hz, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hdiag_only, le_div_iff₀ hn_pos]
    let Iset := (Finset.univ.filter (fun w : Fin n => |x w| ≤ 1 - γ)).erase v
    have hIset_card : (δ / 2) * (n : ℝ) ≤ (Iset.card : ℝ) := by
      have h1 : (Finset.univ.filter (fun w : Fin n => |x w| ≤ 1 - γ)).card ≤ Iset.card + 1 := by
        dsimp only [Iset]
        by_cases hv : v ∈ Finset.univ.filter (fun w : Fin n => |x w| ≤ 1 - γ)
        · have h2 := Finset.card_erase_add_one hv
          omega
        · rw [Finset.erase_eq_of_notMem hv]; omega
      have h1R : ((Finset.univ.filter (fun w : Fin n => |x w| ≤ 1 - γ)).card : ℝ) ≤ (Iset.card : ℝ) + 1 := by
        exact_mod_cast h1
      linarith [hI, h1R, hnδ]
    have hsub : ∑ w ∈ Iset, ((1 / 25 : ℝ) * Nξ) ≤
        ∑ w : Fin n, (c w) ^ 2 * ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ w) ^ 2 := by
      calc ∑ w ∈ Iset, ((1 / 25 : ℝ) * Nξ)
          ≤ ∑ w ∈ Iset, (c w) ^ 2 * ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ w) ^ 2 := by
            refine Finset.sum_le_sum fun w hw => ?_
            have hne : w ≠ v := Finset.ne_of_mem_erase hw
            have hmem : |x w| ≤ 1 - γ := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hw)).2
            have hcw : (c w) ^ 2 = 1 := by
              simp only [c, mul_pow, adjSign_sq_of_ne ω hne.symm, chi_eq_one hγ0 hγ1 hmem]; norm_num
            rw [hcw, one_mul]
            exact sum_stepKickVal_sq_ge hn w
        _ ≤ ∑ w : Fin n, (c w) ^ 2 * ∑ ξ : Fin n → Fin n → Bool, (stepKickVal ξ w) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun w =>
              mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc (δ / 50) * Nξ * (n : ℝ) = ((δ / 2) * (n : ℝ)) * ((1 / 25 : ℝ) * Nξ) := by ring
      _ ≤ (Iset.card : ℝ) * ((1 / 25 : ℝ) * Nξ) := mul_le_mul_of_nonneg_right hIset_card (by positivity)
      _ = ∑ _w ∈ Iset, ((1 / 25 : ℝ) * Nξ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := hsub
  -- Fourth moment upper bound: `∑ (Z0 ξ)^4 ≤ 48 * Nξ`.
  have hE4 : ∑ ξ : Fin n → Fin n → Bool, (Z0 ξ) ^ 4 ≤ 48 * Nξ := by
    have hexp : ∀ ξ, (Z0 ξ) ^ 4 =
        (∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          (c w₁ * c w₂ * c w₃ * c w₄) *
          (stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄)) / (n : ℝ) ^ 2 := by
      intro ξ
      have hsq : (Z0 ξ) ^ 2 = (∑ w : Fin n, c w * stepKickVal ξ w) ^ 2 / (n : ℝ) := by
        simp only [Z0, div_pow, Real.sq_sqrt hn_pos.le]
      have h2 : (∑ w : Fin n, c w * stepKickVal ξ w) ^ 2 =
          ∑ w₁ : Fin n, ∑ w₂ : Fin n, (c w₁ * stepKickVal ξ w₁) * (c w₂ * stepKickVal ξ w₂) := by
        rw [sq, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      rw [show (Z0 ξ) ^ 4 = ((Z0 ξ) ^ 2) ^ 2 by ring, hsq, div_pow, h2]
      congr 1
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w₁ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun w₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w₃ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w₄ _ => by ring
    simp_rw [hexp]
    rw [← Finset.sum_div, div_le_iff₀ (sq_pos_of_pos hn_pos)]
    have hquad_sum : ∑ ξ : Fin n → Fin n → Bool,
        ∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          (c w₁ * c w₂ * c w₃ * c w₄) *
          (stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄) =
        ∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          (c w₁ * c w₂ * c w₃ * c w₄) *
          ∑ ξ : Fin n → Fin n → Bool,
            stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄ := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Fin n → Bool))), ← Finset.mul_sum]
    rw [hquad_sum]
    have hzero_odd : ∀ w₁ w₂ w₃ w₄ : Fin n,
        (¬ ((w₁ = w₂ ∧ w₃ = w₄) ∨ (w₁ = w₃ ∧ w₂ = w₄) ∨ (w₁ = w₄ ∧ w₂ = w₃))) →
        ∑ ξ : Fin n → Fin n → Bool,
          stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄ = 0 := by
      intro w₁ w₂ w₃ w₄ hnot
      have hodd : ∀ a : Fin n,
          (a = w₁ ∧ a ≠ w₂ ∧ a ≠ w₃ ∧ a ≠ w₄) ∨
          (a = w₂ ∧ a ≠ w₁ ∧ a ≠ w₃ ∧ a ≠ w₄) ∨
          (a = w₃ ∧ a ≠ w₁ ∧ a ≠ w₂ ∧ a ≠ w₄) ∨
          (a = w₄ ∧ a ≠ w₁ ∧ a ≠ w₂ ∧ a ≠ w₃) →
          ∑ ξ : Fin n → Fin n → Bool,
            stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄ = 0 := by
        intro a hcase
        refine sum_stepKick_flip_zero a _ fun ξ => ?_
        rcases hcase with ⟨rfl, h2, h3, h4⟩ | ⟨rfl, h1, h3, h4⟩ | ⟨rfl, h1, h2, h4⟩ | ⟨rfl, h1, h2, h3⟩
        · simp [stepKickVal_flipVertexBits, h2.symm, h3.symm, h4.symm]
        · simp [stepKickVal_flipVertexBits, h1.symm, h3.symm, h4.symm]
        · simp [stepKickVal_flipVertexBits, h1.symm, h2.symm, h4.symm]
        · simp [stepKickVal_flipVertexBits, h1.symm, h2.symm, h3.symm]
      by_cases h12 : w₁ = w₂
      · have h34 : w₃ ≠ w₄ := fun h => hnot (Or.inl ⟨h12, h⟩)
        by_cases h13 : w₁ = w₃
        · exact hodd w₄ (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [h13]; exact h34.symm,
            by rw [← h12, h13]; exact h34.symm, h34.symm⟩)))
        · exact hodd w₃ (Or.inr (Or.inr (Or.inl ⟨rfl, Ne.symm h13,
            by rw [← h12]; exact Ne.symm h13, h34⟩)))
      · by_cases h13 : w₁ = w₃
        · have h24 : w₂ ≠ w₄ := fun h => hnot (Or.inr (Or.inl ⟨h13, h⟩))
          exact hodd w₂ (Or.inr (Or.inl ⟨rfl, Ne.symm h12,
            by rw [← h13]; exact Ne.symm h12, h24⟩))
        · by_cases h14 : w₁ = w₄
          · have h23 : w₂ ≠ w₃ := fun h => hnot (Or.inr (Or.inr ⟨h14, h⟩))
            exact hodd w₂ (Or.inr (Or.inl ⟨rfl, Ne.symm h12, h23,
              by rw [← h14]; exact Ne.symm h12⟩))
          · exact hodd w₁ (Or.inl ⟨rfl, h12, h13, h14⟩)
    have hterm_le : ∀ w₁ w₂ w₃ w₄ : Fin n,
        (c w₁ * c w₂ * c w₃ * c w₄) *
          (∑ ξ : Fin n → Fin n → Bool,
            stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄) ≤
        ((if w₁ = w₂ ∧ w₃ = w₄ then (16 : ℝ) else 0) +
         (if w₁ = w₃ ∧ w₂ = w₄ then (16 : ℝ) else 0) +
         (if w₁ = w₄ ∧ w₂ = w₃ then (16 : ℝ) else 0)) * Nξ := by
      intro w₁ w₂ w₃ w₄
      by_cases hp : (w₁ = w₂ ∧ w₃ = w₄) ∨ (w₁ = w₃ ∧ w₂ = w₄) ∨ (w₁ = w₄ ∧ w₂ = w₃)
      · have hprod_c : |c w₁ * c w₂ * c w₃ * c w₄| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_mul]
          have h12 := mul_le_mul (hc_bd w₁) (hc_bd w₂) (abs_nonneg _) zero_le_one
          have h123 := mul_le_mul h12 (hc_bd w₃) (abs_nonneg _) (by norm_num)
          exact (mul_le_mul h123 (hc_bd w₄) (abs_nonneg _) (by norm_num)).trans (by norm_num)
        have hsum_bd : |∑ ξ : Fin n → Fin n → Bool,
            stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄| ≤ 16 * Nξ := by
          calc _ ≤ ∑ ξ : Fin n → Fin n → Bool,
                |stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _ξ : Fin n → Fin n → Bool, (16 : ℝ) := Finset.sum_le_sum fun ξ _ => by
                rw [abs_mul, abs_mul, abs_mul]
                have h1 := mul_le_mul (abs_stepKickVal_lt_two ξ w₁).le (abs_stepKickVal_lt_two ξ w₂).le
                  (abs_nonneg _) zero_le_two
                have h2 := mul_le_mul h1 (abs_stepKickVal_lt_two ξ w₃).le (abs_nonneg _) (by norm_num)
                exact (mul_le_mul h2 (abs_stepKickVal_lt_two ξ w₄).le (abs_nonneg _) (by norm_num)).trans
                  (by norm_num)
            _ = 16 * Nξ := by simp [Nξ, mul_comm]
        have hle16 : (c w₁ * c w₂ * c w₃ * c w₄) *
            (∑ ξ : Fin n → Fin n → Bool,
              stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄) ≤ 16 * Nξ := by
          calc _ ≤ |(c w₁ * c w₂ * c w₃ * c w₄) *
                (∑ ξ : Fin n → Fin n → Bool,
                  stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄)| := le_abs_self _
            _ = |c w₁ * c w₂ * c w₃ * c w₄| * |∑ ξ : Fin n → Fin n → Bool,
                  stepKickVal ξ w₁ * stepKickVal ξ w₂ * stepKickVal ξ w₃ * stepKickVal ξ w₄| := abs_mul _ _
            _ ≤ 1 * (16 * Nξ) := mul_le_mul hprod_c hsum_bd (abs_nonneg _) zero_le_one
            _ = 16 * Nξ := one_mul _
        have hge16 : (16 : ℝ) ≤ (if w₁ = w₂ ∧ w₃ = w₄ then (16 : ℝ) else 0) +
            (if w₁ = w₃ ∧ w₂ = w₄ then (16 : ℝ) else 0) +
            (if w₁ = w₄ ∧ w₂ = w₃ then (16 : ℝ) else 0) := by
          rcases hp with h | h | h <;> simp [h] <;> split_ifs <;> linarith
        exact hle16.trans (mul_le_mul_of_nonneg_right hge16 hNξ_pos.le)
      · rw [hzero_odd w₁ w₂ w₃ w₄ hp, mul_zero]; positivity
    have hsum_ind : ∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
        ((if w₁ = w₂ ∧ w₃ = w₄ then (16 : ℝ) else 0) +
         (if w₁ = w₃ ∧ w₂ = w₄ then (16 : ℝ) else 0) +
         (if w₁ = w₄ ∧ w₂ = w₃ then (16 : ℝ) else 0)) = 48 * (n : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, ite_and]
      have hA : (∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          if w₁ = w₂ then if w₃ = w₄ then (16 : ℝ) else 0 else 0) = 16 * (n : ℝ) ^ 2 := by
        simp [sq]; ring
      have hB : (∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          if w₁ = w₃ then if w₂ = w₄ then (16 : ℝ) else 0 else 0) = 16 * (n : ℝ) ^ 2 := by
        simp [sq]; ring
      have hC : (∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
          if w₁ = w₄ then if w₂ = w₃ then (16 : ℝ) else 0 else 0) = 16 * (n : ℝ) ^ 2 := by
        simp [sq]; ring
      linarith [hA, hB, hC]
    calc _ ≤ ∑ w₁ : Fin n, ∑ w₂ : Fin n, ∑ w₃ : Fin n, ∑ w₄ : Fin n,
            ((if w₁ = w₂ ∧ w₃ = w₄ then (16 : ℝ) else 0) +
             (if w₁ = w₃ ∧ w₂ = w₄ then (16 : ℝ) else 0) +
             (if w₁ = w₄ ∧ w₂ = w₃ then (16 : ℝ) else 0)) * Nξ :=
          Finset.sum_le_sum fun w₁ _ => Finset.sum_le_sum fun w₂ _ =>
            Finset.sum_le_sum fun w₃ _ => Finset.sum_le_sum fun w₄ _ => hterm_le w₁ w₂ w₃ w₄
      _ = (48 * (n : ℝ) ^ 2) * Nξ := by simp_rw [← Finset.sum_mul, hsum_ind]
      _ = 48 * Nξ * (n : ℝ) ^ 2 := by ring
  -- Paley–Zygmund on `Z0^2` at `δ / 200`.
  let GoodZ := Finset.univ.filter (fun ξ : Fin n → Fin n → Bool => δ / 200 ≤ (Z0 ξ) ^ 2)
  have hPZ : (δ ^ 2 / 300000) * Nξ ≤ (GoodZ.card : ℝ) := by
    have hsplit : (3 * δ / 200) * Nξ ≤ ∑ ξ ∈ GoodZ, (Z0 ξ) ^ 2 := by
      have hcov : ∑ ξ : Fin n → Fin n → Bool, (Z0 ξ) ^ 2 =
          (∑ ξ ∈ GoodZ, (Z0 ξ) ^ 2) + ∑ ξ ∈ Finset.univ \ GoodZ, (Z0 ξ) ^ 2 :=
        (Finset.sum_add_sum_compl GoodZ (fun ξ => (Z0 ξ) ^ 2)).symm
      have hbad : ∑ ξ ∈ Finset.univ \ GoodZ, (Z0 ξ) ^ 2 ≤ (δ / 200) * Nξ := by
        calc ∑ ξ ∈ Finset.univ \ GoodZ, (Z0 ξ) ^ 2
            ≤ ∑ _ξ ∈ Finset.univ \ GoodZ, (δ / 200) := Finset.sum_le_sum fun ξ hξ => by
              have hnot : ¬ δ / 200 ≤ (Z0 ξ) ^ 2 := fun h =>
                (Finset.mem_sdiff.mp hξ).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
              linarith
          _ = ((Finset.univ \ GoodZ).card : ℝ) * (δ / 200) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ Nξ * (δ / 200) := mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (Finset.card_le_univ (Finset.univ \ GoodZ))) (by positivity)
          _ = (δ / 200) * Nξ := mul_comm _ _
      linarith [hE2, hcov, hbad]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq GoodZ (fun _ => (1 : ℝ)) (fun ξ => (Z0 ξ) ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have h4sub : ∑ ξ ∈ GoodZ, ((Z0 ξ) ^ 2) ^ 2 ≤ 48 * Nξ := by
      have hrew : ∀ ξ, ((Z0 ξ) ^ 2) ^ 2 = (Z0 ξ) ^ 4 := fun _ => by ring
      simp_rw [hrew]
      exact (Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity).trans hE4
    have hsq_ge : ((3 * δ / 200) * Nξ) ^ 2 ≤ (GoodZ.card : ℝ) * (48 * Nξ) :=
      (pow_le_pow_left₀ (by positivity) hsplit 2).trans
        (hcs.trans (mul_le_mul_of_nonneg_left h4sub (Nat.cast_nonneg _)))
    have hnum : (δ ^ 2 / 300000) * Nξ * (48 * Nξ) ≤ ((3 * δ / 200) * Nξ) ^ 2 := by
      have hcoeff : (48 / 300000 : ℝ) ≤ (9 / 40000 : ℝ) := by norm_num
      have hnn : 0 ≤ δ ^ 2 * Nξ ^ 2 := by positivity
      have h1 : (δ ^ 2 / 300000) * Nξ * (48 * Nξ) = (48 / 300000 : ℝ) * (δ ^ 2 * Nξ ^ 2) := by ring
      have h2 : ((3 * δ / 200) * Nξ) ^ 2 = (9 / 40000 : ℝ) * (δ ^ 2 * Nξ ^ 2) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hcoeff hnn
    have h48pos : 0 < 48 * Nξ := by positivity
    nlinarith only [hsq_ge, hnum, h48pos]
  -- Sign symmetry `ξ ↦ !ξ`: at least half of `GoodZ` escapes `|iterGrad ω (xt ξ) v| ≥ σ √(δ / 200)`.
  let negAll : (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) := fun ξ u j => !(ξ u j)
  have hZ0_neg : ∀ ξ, Z0 (negAll ξ) = -Z0 ξ := fun ξ => by
    simp only [Z0]
    have hW_neg : ∀ w, stepKickVal (negAll ξ) w = -stepKickVal ξ w := fun w => by
      simp only [stepKickVal, negAll]
      have hsum : (∑ j : Fin n, if !(ξ w j) then (1 : ℝ) else -1) =
          -(∑ j : Fin n, if ξ w j then (1 : ℝ) else -1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by cases ξ w j <;> norm_num
      rw [hsum, neg_div, tau_neg]
    have hsum : ∑ w : Fin n, c w * stepKickVal (negAll ξ) w =
        -(∑ w : Fin n, c w * stepKickVal ξ w) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => by rw [hW_neg w]; ring
    rw [hsum, neg_div]
  let S_esc := Finset.univ.filter (fun ξ : Fin n → Fin n → Bool =>
    σ * Real.sqrt (δ / 200) ≤ |iterGrad ω (xt ξ) v|)
  have hcov : GoodZ ⊆ S_esc ∪ S_esc.image negAll := by
    intro ξ hξ
    have hZsq : δ / 200 ≤ (Z0 ξ) ^ 2 := (Finset.mem_filter.mp hξ).2
    have hZabs : Real.sqrt (δ / 200) ≤ |Z0 ξ| := by
      have h1 := Real.sqrt_le_sqrt hZsq
      rwa [Real.sqrt_sq_eq_abs] at h1
    have htri : 2 * (σ * |Z0 ξ|) ≤ |iterGrad ω x v + σ * Z0 ξ| + |iterGrad ω x v - σ * Z0 ξ| := by
      have h1 := abs_sub (iterGrad ω x v + σ * Z0 ξ) (iterGrad ω x v - σ * Z0 ξ)
      have h2 : (iterGrad ω x v + σ * Z0 ξ) - (iterGrad ω x v - σ * Z0 ξ) = 2 * (σ * Z0 ξ) := by ring
      rw [h2, abs_mul, abs_of_pos two_pos, abs_mul, abs_of_pos hσ0] at h1
      exact h1
    rcases le_or_gt (σ * Real.sqrt (δ / 200)) |iterGrad ω x v + σ * Z0 ξ| with hpos | hneg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hgrad_split]⟩)
    · have hother : σ * Real.sqrt (δ / 200) ≤ |iterGrad ω x v - σ * Z0 ξ| := by
        have hmul : σ * Real.sqrt (δ / 200) ≤ σ * |Z0 ξ| := mul_le_mul_of_nonneg_left hZabs hσ0.le
        linarith [htri, hneg, hmul]
      have hmem_neg : negAll ξ ∈ S_esc := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hgrad_split, hZ0_neg]
        simpa [sub_eq_add_neg] using hother
      have hinv : negAll (negAll ξ) = ξ := by funext u j; simp [negAll]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨negAll ξ, hmem_neg, hinv⟩)
  have h2card : (GoodZ.card : ℝ) ≤ 2 * (S_esc.card : ℝ) := by
    have hnat : GoodZ.card ≤ 2 * S_esc.card := by
      calc GoodZ.card ≤ (S_esc ∪ S_esc.image negAll).card := Finset.card_le_card hcov
        _ ≤ S_esc.card + (S_esc.image negAll).card := Finset.card_union_le _ _
        _ ≤ S_esc.card + S_esc.card := Nat.add_le_add_left Finset.card_image_le _
        _ = 2 * S_esc.card := by omega
    exact_mod_cast hnat
  linarith [hPZ, h2card]

/-- Deterministic step-size lower bound from a large gradient at an interior vertex. -/
lemma abs_psi_sub_ge_of_grad {lam γ σ δ xt g : ℝ} (hlam : 0 < lam)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (_hσ0 : 0 < σ) (_hδ0 : 0 < δ)
    (hxt : |xt| ≤ 1 - γ / 4)
    (hgrad : σ * Real.sqrt (δ / 200) ≤ |g|)
    (hlam_small : 16 * lam / γ ≤ (1 / 40) * σ * Real.sqrt (δ / 200)) :
    min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200)) ≤
      |psi lam (xt + (1 / 20 : ℝ) * g) - xt| := by
  set x' := psi lam (xt + (1 / 20 : ℝ) * g)
  rcases le_or_gt (1 - γ / 8) |x'| with hout | hin
  · have htri := abs_sub_abs_le_abs_sub x' xt
    exact (min_le_left _ _).trans (by linarith [htri, hout, hxt])
  · have hinv_bd : |hInv lam x' - x'| ≤ 16 * lam / γ := by
      have h1 := abs_hInv_sub_le hlam (by linarith : 0 < γ / 4) (by linarith : γ / 4 ≤ 1)
        (by linarith : |x'| ≤ 1 - (γ / 4) / 2)
      have h2 : 4 * lam / (γ / 4) = 16 * lam / γ := by ring
      rwa [h2] at h1
    have hinv_eq : hInv lam x' = xt + (1 / 20 : ℝ) * g := hInv_psi hlam _
    have htri : (1 / 20 : ℝ) * |g| ≤ |hInv lam x' - x'| + |x' - xt| := by
      have h1 : (1 / 20 : ℝ) * g = (hInv lam x' - x') + (x' - xt) := by linarith [hinv_eq]
      have h2 := abs_add_le (hInv lam x' - x') (x' - xt)
      rw [← h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)] at h2
      exact h2
    exact (min_le_right _ _).trans (by linarith [htri, hinv_bd, hgrad, hlam_small])

/-- Pointwise Markov bound on the kick coordinates: for ANY good graph `ω ∈ G_op`,
with probability `≥ 1 - 61 / (T * min c_esc (5 δ₁))` over `ζ`, some step `s < T` has
BOTH `< δ n` interior vertices AND `‖x_{s+1} - xt_s‖_2^2 < δ₁ n`. -/
theorem pointwise_good_step_prob {T n : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T)
    {lam γ σ δ δ₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 4)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hσ0 : 0 < σ) (hσ : σ ≤ γ / 8)
    (hδ0 : 0 < δ) (hδ₁0 : 0 < δ₁) (hnδ : 2 ≤ δ * (n : ℝ))
    (hlam_grad : 16 * lam / γ ≤ (1 / 40) * σ * Real.sqrt (δ / 200))
    (hlam_drift : (T : ℝ) * (320 * lam * σ / γ) ≤ 1)
    (ω : EdgeIdx n → Bool)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ)) :
    let d₀ : ℝ := min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200))
    let c_esc : ℝ := 5 * δ * (δ ^ 2 / 600000) * d₀ ^ 2
    ((Finset.univ.filter (fun ζ : KickBits T n =>
      ∀ s : Fin T,
        δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ) ∨
        δ₁ * (n : ℝ) ≤ ∑ v : Fin n,
          (iterState lam γ σ ω ζ (s.val + 1) v -
            iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2)).card : ℝ) ≤
      (61 / ((T : ℝ) * min c_esc (5 * δ₁))) * (Fintype.card (KickBits T n) : ℝ) := by
  intro d₀ c_esc
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd₀_pos : 0 < d₀ := lt_min (by linarith) (by positivity)
  have hcesc_pos : 0 < c_esc := by positivity
  have hmin_pos : 0 < min c_esc (5 * δ₁) := lt_min hcesc_pos (by positivity)
  let E : (Fin n → ℝ) → ℝ := fun z =>
    (∑ i : Fin n, ∑ j : Fin n, z i * adjSign ω i j * z j) / (2 * Real.sqrt (n : ℝ)) -
      ∑ i : Fin n, R_bar lam (1 / 20) (z i)
  -- Energy bounds: `-50 n ≤ E(z) ≤ 10 n` for all `z ∈ (-1, 1)^n`.
  have hE_bd : ∀ z : Fin n → ℝ, (∀ v, |z v| < 1) → -50 * (n : ℝ) ≤ E z ∧ E z ≤ 10 * (n : ℝ) := by
    intro z hz
    have hzn : ∑ v : Fin n, (z v / Real.sqrt (n : ℝ)) ^ 2 ≤ 1 := by
      simp_rw [div_pow, Real.sq_sqrt hn_pos.le, ← Finset.sum_div]
      rw [div_le_one hn_pos]
      calc ∑ v : Fin n, (z v) ^ 2 ≤ ∑ _v : Fin n, (1 : ℝ) := Finset.sum_le_sum fun v _ => by
            have := abs_lt.mp (hz v); nlinarith
        _ = (n : ℝ) := by simp
    have hquad_abs : |∑ i : Fin n, ∑ j : Fin n, z i * adjSign ω i j * z j| ≤ 20 * (n : ℝ) * Real.sqrt (n : ℝ) := by
      have h1 := hop (fun i => z i / Real.sqrt (n : ℝ)) (fun j => z j / Real.sqrt (n : ℝ)) hzn hzn
      have hfac : (∑ i : Fin n, ∑ j : Fin n, (z i / Real.sqrt (n : ℝ)) * adjSign ω i j * (z j / Real.sqrt (n : ℝ))) =
          (∑ i : Fin n, ∑ j : Fin n, z i * adjSign ω i j * z j) / (n : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => by
          field_simp; rw [Real.sq_sqrt hn_pos.le]; ring
      rw [hfac, abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos] at h1
      linarith
    have hq_bd : |(∑ i : Fin n, ∑ j : Fin n, z i * adjSign ω i j * z j) / (2 * Real.sqrt (n : ℝ))| ≤ 10 * (n : ℝ) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (n : ℝ)),
        div_le_iff₀ (by positivity)]
      linarith [hquad_abs]
    have hR_nn : 0 ≤ ∑ i : Fin n, R_bar lam (1 / 20) (z i) :=
      Finset.sum_nonneg fun i _ => (R_bar_bounds hlam hlam1 (by norm_num : (0 : ℝ) < 1 / 20) (hz i)).1
    have hR_le : ∑ i : Fin n, R_bar lam (1 / 20) (z i) ≤ 40 * (n : ℝ) := by
      calc _ ≤ ∑ _i : Fin n, (40 : ℝ) := Finset.sum_le_sum fun i _ => by
            have := (R_bar_bounds hlam hlam1 (by norm_num : (0 : ℝ) < 1 / 20) (hz i)).2
            linarith
        _ = 40 * (n : ℝ) := by simp [mul_comm]
    have hq := abs_le.mp hq_bd
    simp only [E]; constructor <;> linarith
  -- Per-step expected energy increase lower bound for any `s : Fin T`.
  have hstep : ∀ s : Fin T,
      ∑ ζ : KickBits T n,
          (5 * ∑ v : Fin n,
            (iterState lam γ σ ω ζ (s.val + 1) v -
              iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 +
          if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
              |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ)
            then c_esc * (n : ℝ) else 0) ≤
        (∑ ζ : KickBits T n,
          (E (iterState lam γ σ ω ζ (s.val + 1)) - E (iterState lam γ σ ω ζ s.val))) +
        (320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
    intro s
    -- Factor `ζ : KickBits T n` into `(ζ s, rest)` where `iterState ... s` depends only on `rest`.
    let eS : KickBits T n ≃ (Fin n → Fin n → Bool) × ({t : Fin T // t ≠ s} → Fin n → Fin n → Bool) :=
      { toFun := fun ζ => (ζ s, fun t => ζ t.1)
        invFun := fun p t => if h : t = s then p.1 else p.2 ⟨t, h⟩
        left_inv := fun ζ => by funext t v j; by_cases h : t = s <;> simp [h]
        right_inv := fun ⟨a, b⟩ => by
          apply Prod.ext
          · funext v j; simp
          · funext t v j; simp [t.2] }
    -- `iterState ... k` is independent of `ζ s` for all `k ≤ s.val`.
    have hindep : ∀ (k : ℕ), k ≤ s.val → ∀ (a₁ a₂ : Fin n → Fin n → Bool)
        (b : {t : Fin T // t ≠ s} → Fin n → Fin n → Bool),
        iterState lam γ σ ω (eS.symm (a₁, b)) k = iterState lam γ σ ω (eS.symm (a₂, b)) k := by
      intro k
      induction k with
      | zero => intro _ _ _ _; rfl
      | succ k ih =>
        intro hk a₁ a₂ b
        have hprev := ih (by omega) a₁ a₂ b
        funext v
        change iterStep lam γ σ ω (eS.symm (a₁, b)) k (iterState lam γ σ ω (eS.symm (a₁, b)) k) v =
          iterStep lam γ σ ω (eS.symm (a₂, b)) k (iterState lam γ σ ω (eS.symm (a₂, b)) k) v
        rw [hprev]
        have hkt : iterKick γ σ (eS.symm (a₁, b)) k (iterState lam γ σ ω (eS.symm (a₂, b)) k) =
            iterKick γ σ (eS.symm (a₂, b)) k (iterState lam γ σ ω (eS.symm (a₂, b)) k) := by
          funext w
          simp only [iterKick, kickVal]
          split_ifs with hlt
          · have hne : (⟨k, hlt⟩ : Fin T) ≠ s := fun h => by
              have : k = s.val := congrArg Fin.val h; omega
            simp [eS, hne]
          · rfl
        simp only [iterStep, hkt]
    rw [← Equiv.sum_comp eS.symm, ← Equiv.sum_comp eS.symm, Fintype.sum_prod_type, Fintype.sum_prod_type]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => arg 1; rw [Finset.sum_comm]
    have hcard_eS : (Fintype.card (KickBits T n) : ℝ) =
        ∑ _b : {t : Fin T // t ≠ s} → Fin n → Fin n → Bool,
          (Fintype.card (Fin n → Fin n → Bool) : ℝ) := by
      have h1 := Fintype.card_congr eS
      rw [Fintype.card_prod] at h1
      rw [h1, Nat.cast_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    rw [hcard_eS, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    -- Fix `b`; let `x := iterState ... (eS.symm (default, b)) s.val`.
    let x : Fin n → ℝ := iterState lam γ σ ω (eS.symm (fun _ _ => false, b)) s.val
    have hx_eq : ∀ ξ : Fin n → Fin n → Bool,
        iterState lam γ σ ω (eS.symm (ξ, b)) s.val = x :=
      fun ξ => hindep s.val le_rfl ξ (fun _ _ => false) b
    have hx_lt : ∀ v, |x v| < 1 := fun v => abs_iterState_lt_one hlam ω _ s.val v
    let xt : (Fin n → Fin n → Bool) → Fin n → ℝ :=
      fun ξ v => x v + σ * chi γ (x v) * stepKickVal ξ v
    have hxt_eq : ∀ ξ : Fin n → Fin n → Bool,
        iterKick γ σ (eS.symm (ξ, b)) s.val (iterState lam γ σ ω (eS.symm (ξ, b)) s.val) = xt ξ := by
      intro ξ; funext v
      rw [hx_eq ξ]
      simp [iterKick, xt, kickVal, stepKickVal, eS]
    have hx'_eq : ∀ ξ : Fin n → Fin n → Bool,
        iterState lam γ σ ω (eS.symm (ξ, b)) (s.val + 1) =
        fun v => psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) := by
      intro ξ; funext v
      change psi lam (iterKick γ σ (eS.symm (ξ, b)) s.val (iterState lam γ σ ω (eS.symm (ξ, b)) s.val) v +
        (1 / 20 : ℝ) * iterGrad ω (iterKick γ σ (eS.symm (ξ, b)) s.val
          (iterState lam γ σ ω (eS.symm (ξ, b)) s.val)) v) = _
      rw [hxt_eq ξ]
    -- Proximal ascent at every `ξ`.
    have hprox : ∀ ξ : Fin n → Fin n → Bool,
        10 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 ≤
        E (fun v => psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v)) - E (xt ξ) := by
      intro ξ
      have hxt_lt : ∀ v, |xt ξ v| < 1 := fun v => by
        rw [← hxt_eq ξ, hx_eq ξ]
        exact abs_iterKick_lt_one hγ0 hγ1 hσ0.le hσ _ s.val x v (hx_lt v)
      exact prox_ascent_step hn hlam ω hop (xt ξ) hxt_lt
    -- Barrier drift bound on `E (xt ξ) - E x` summed over `ξ`.
    have hkick_E : -(320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) ≤
        ∑ ξ : Fin n → Fin n → Bool, (E (xt ξ) - E x) := by
      have hquad := kick_quad_avg_zero ω γ σ x
      have hq_diff : ∑ ξ : Fin n → Fin n → Bool,
          ((∑ i : Fin n, ∑ j : Fin n, xt ξ i * adjSign ω i j * xt ξ j) / (2 * Real.sqrt (n : ℝ)) -
           (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) / (2 * Real.sqrt (n : ℝ))) = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, hquad, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_div_assoc, sub_self]
      have hR_diff : ∀ ξ : Fin n → Fin n → Bool,
          ∑ v : Fin n, (R_bar lam (1 / 20) (xt ξ v) - R_bar lam (1 / 20) (x v)) ≤
            (320 * lam * σ / γ) * (n : ℝ) := by
        intro ξ
        calc ∑ v : Fin n, (R_bar lam (1 / 20) (xt ξ v) - R_bar lam (1 / 20) (x v))
            ≤ ∑ _v : Fin n, (320 * lam * σ / γ) := Finset.sum_le_sum fun v _ => by
              rcases le_or_gt (1 - γ / 2) |x v| with hout | hin
              · have heq : xt ξ v = x v := by simp [xt, chi_eq_zero hγ0 hγ1 hout]
                rw [heq, sub_self]; positivity
              · have hxt_in : |xt ξ v| ≤ 1 - γ / 4 := by
                  rw [← hxt_eq ξ, hx_eq ξ]
                  exact abs_iterKick_interior hσ0.le hσ _ s.val x v hin.le
                have hlip := R_bar_sub_le_of_interior hlam (by norm_num : (0 : ℝ) < 1 / 20)
                  (by linarith : 0 < γ / 2) (by linarith : γ / 2 ≤ 1)
                  (by linarith : |x v| ≤ 1 - (γ / 2) / 2)
                  (by linarith : |xt ξ v| ≤ 1 - (γ / 2) / 2)
                have hdiff : |xt ξ v - x v| ≤ 2 * σ := by
                  have h1 : xt ξ v - x v = σ * chi γ (x v) * stepKickVal ξ v := by simp [xt]
                  rw [h1, abs_mul, abs_mul, abs_of_pos hσ0, abs_of_nonneg (chi_bounds γ (x v)).1]
                  calc σ * chi γ (x v) * |stepKickVal ξ v|
                      ≤ σ * 1 * 2 := mul_le_mul (mul_le_mul_of_nonneg_left (chi_bounds γ (x v)).2 hσ0.le)
                        (abs_stepKickVal_lt_two ξ v).le (abs_nonneg _) (by positivity)
                    _ = 2 * σ := by ring
                have hconst : (4 * lam / ((1 / 20 : ℝ) * (γ / 2))) * (2 * σ) = 320 * lam * σ / γ := by ring
                have hbd := (le_abs_self _).trans (hlip.trans
                  (mul_le_mul_of_nonneg_left hdiff (by positivity)))
                linarith [hbd, hconst]
          _ = (320 * lam * σ / γ) * (n : ℝ) := by simp [mul_comm]
      have hE_split : ∑ ξ : Fin n → Fin n → Bool, (E (xt ξ) - E x) =
          (∑ ξ : Fin n → Fin n → Bool,
            ((∑ i : Fin n, ∑ j : Fin n, xt ξ i * adjSign ω i j * xt ξ j) / (2 * Real.sqrt (n : ℝ)) -
             (∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * x j) / (2 * Real.sqrt (n : ℝ)))) -
          ∑ ξ : Fin n → Fin n → Bool, ∑ v : Fin n, (R_bar lam (1 / 20) (xt ξ v) - R_bar lam (1 / 20) (x v)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        simp only [E, Finset.sum_sub_distrib]; ring
      rw [hE_split, hq_diff, zero_sub]
      have hsumR : ∑ ξ : Fin n → Fin n → Bool,
          ∑ v : Fin n, (R_bar lam (1 / 20) (xt ξ v) - R_bar lam (1 / 20) (x v)) ≤
          (320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) := by
        calc _ ≤ ∑ _ξ : Fin n → Fin n → Bool, ((320 * lam * σ / γ) * (n : ℝ)) :=
              Finset.sum_le_sum fun ξ _ => hR_diff ξ
          _ = (320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      linarith [hsumR]
    -- Escape lower bound for the second half `5 * ∑ (x' - xt)^2` when `|I| ≥ δ n`.
    have hesc : ∑ _ξ : Fin n → Fin n → Bool,
        (if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n => |x v| ≤ 1 - γ)).card : ℝ)
          then c_esc * (n : ℝ) else 0) ≤
        ∑ ξ : Fin n → Fin n → Bool,
          5 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := by
      by_cases hI : δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n => |x v| ≤ 1 - γ)).card : ℝ)
      · rw [if_pos hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        let Iset := Finset.univ.filter (fun v : Fin n => |x v| ≤ 1 - γ)
        have hper_v : ∀ v ∈ Iset,
            (δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) * d₀ ^ 2 ≤
              ∑ ξ : Fin n → Fin n → Bool,
                (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := by
          intro v hv
          have hv_in : |x v| ≤ 1 - γ := (Finset.mem_filter.mp hv).2
          have hcard_esc := kick_single_vertex_escape hn ω hγ0 hγ1 hσ0 hδ0 hnδ x v hI
          let S_esc := Finset.univ.filter (fun ξ : Fin n → Fin n → Bool =>
            σ * Real.sqrt (δ / 200) ≤ |iterGrad ω (xt ξ) v|)
          have hge_d0 : ∀ ξ ∈ S_esc, d₀ ^ 2 ≤
              (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := by
            intro ξ hξ
            have hgrad_ge : σ * Real.sqrt (δ / 200) ≤ |iterGrad ω (xt ξ) v| := (Finset.mem_filter.mp hξ).2
            have hxt_in : |xt ξ v| ≤ 1 - γ / 4 := by
              rw [← hxt_eq ξ, hx_eq ξ]
              exact abs_iterKick_interior hσ0.le hσ _ s.val x v (by linarith)
            have h1 := abs_psi_sub_ge_of_grad hlam hγ0 hγ1 hσ0 hδ0 hxt_in hgrad_ge hlam_grad
            have h2 := pow_le_pow_left₀ hd₀_pos.le h1 2
            rwa [sq_abs] at h2
          calc (δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) * d₀ ^ 2
              ≤ (S_esc.card : ℝ) * d₀ ^ 2 := mul_le_mul_of_nonneg_right hcard_esc (sq_nonneg d₀)
            _ = ∑ _ξ ∈ S_esc, d₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ ξ ∈ S_esc, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 :=
                Finset.sum_le_sum hge_d0
            _ ≤ ∑ ξ : Fin n → Fin n → Bool,
                  (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 :=
                Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
        have hsum_v : (Fintype.card (Fin n → Fin n → Bool) : ℝ) * (c_esc * (n : ℝ)) ≤
            5 * ∑ v ∈ Iset, ∑ ξ : Fin n → Fin n → Bool,
              (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := by
          calc (Fintype.card (Fin n → Fin n → Bool) : ℝ) * (c_esc * (n : ℝ))
              = 5 * (δ * (n : ℝ)) * ((δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) * d₀ ^ 2) := by
                simp only [c_esc]; ring
            _ ≤ 5 * (Iset.card : ℝ) * ((δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) * d₀ ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI (by norm_num)) (by positivity)
            _ = 5 * ∑ _v ∈ Iset, ((δ ^ 2 / 600000) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) * d₀ ^ 2) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
            _ ≤ 5 * ∑ v ∈ Iset, ∑ ξ : Fin n → Fin n → Bool,
                  (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper_v) (by norm_num)
        calc (Fintype.card (Fin n → Fin n → Bool) : ℝ) * (c_esc * (n : ℝ))
            ≤ 5 * ∑ v ∈ Iset, ∑ ξ : Fin n → Fin n → Bool,
                (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := hsum_v
          _ ≤ 5 * ∑ v : Fin n, ∑ ξ : Fin n → Fin n → Bool,
                (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg fun _ =>
                Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
          _ = ∑ ξ : Fin n → Fin n → Bool,
                5 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2 := by
              rw [Finset.sum_comm, Finset.mul_sum]
      · rw [if_neg hI, Finset.sum_const_zero]
        exact Finset.sum_nonneg fun _ _ => mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    -- Combine `hprox`, `hesc`, and `hkick_E`!
    have hsum_prox : ∑ ξ : Fin n → Fin n → Bool,
        (5 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2) +
        ∑ ξ : Fin n → Fin n → Bool,
          (5 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2) ≤
        ∑ ξ : Fin n → Fin n → Bool,
          (E (fun v => psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v)) - E (xt ξ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun ξ _ => by linarith [hprox ξ]
    have hLHS_eq : ∑ ξ : Fin n → Fin n → Bool,
        (5 * ∑ v : Fin n,
          (iterState lam γ σ ω (eS.symm (ξ, b)) (s.val + 1) v -
            iterKick γ σ (eS.symm (ξ, b)) s.val (iterState lam γ σ ω (eS.symm (ξ, b)) s.val) v) ^ 2 +
        if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
            |iterState lam γ σ ω (eS.symm (ξ, b)) s.val v| ≤ 1 - γ)).card : ℝ)
          then c_esc * (n : ℝ) else 0) =
        (∑ ξ : Fin n → Fin n → Bool,
          5 * ∑ v : Fin n, (psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v) - xt ξ v) ^ 2) +
        (∑ _ξ : Fin n → Fin n → Bool,
          if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n => |x v| ≤ 1 - γ)).card : ℝ)
            then c_esc * (n : ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun ξ _ => ?_
      · rw [hx'_eq ξ, hxt_eq ξ]
      · simp only [hx_eq ξ]
    have hRHS_eq : ∑ ξ : Fin n → Fin n → Bool,
        (E (iterState lam γ σ ω (eS.symm (ξ, b)) (s.val + 1)) -
          E (iterState lam γ σ ω (eS.symm (ξ, b)) s.val)) =
        (∑ ξ : Fin n → Fin n → Bool,
          (E (fun v => psi lam (xt ξ v + (1 / 20 : ℝ) * iterGrad ω (xt ξ) v)) - E (xt ξ))) +
        (∑ ξ : Fin n → Fin n → Bool, (E (xt ξ) - E x)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      rw [hx'_eq ξ, hx_eq ξ]; ring
    rw [hLHS_eq, hRHS_eq]
    linarith [hsum_prox, hesc, hkick_E]
  -- Telescope `hstep` over all `s : Fin T` and apply Markov!
  have htot : ∑ ζ : KickBits T n, ∑ s : Fin T,
      (5 * ∑ v : Fin n,
        (iterState lam γ σ ω ζ (s.val + 1) v -
          iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 +
      if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ)
        then c_esc * (n : ℝ) else 0) ≤
      61 * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
    rw [Finset.sum_comm]
    have h1 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hstep s
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hE_tele : ∑ s : Fin T, ∑ ζ : KickBits T n,
        (E (iterState lam γ σ ω ζ (s.val + 1)) - E (iterState lam γ σ ω ζ s.val)) ≤
        60 * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
      rw [Finset.sum_comm]
      calc ∑ ζ : KickBits T n, ∑ s : Fin T,
            (E (iterState lam γ σ ω ζ (s.val + 1)) - E (iterState lam γ σ ω ζ s.val))
          = ∑ ζ : KickBits T n, (E (iterState lam γ σ ω ζ T) - E (iterState lam γ σ ω ζ 0)) := by
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Fin.sum_univ_eq_sum_range (fun k => E (iterState lam γ σ ω ζ (k + 1)) -
              E (iterState lam γ σ ω ζ k)) T]
            exact Finset.sum_range_sub (fun k => E (iterState lam γ σ ω ζ k)) T
        _ ≤ ∑ _ζ : KickBits T n, (60 * (n : ℝ)) := Finset.sum_le_sum fun ζ _ => by
            have hT_bd := hE_bd (iterState lam γ σ ω ζ T) (abs_iterState_lt_one hlam ω ζ T)
            have h0_bd := hE_bd (iterState lam γ σ ω ζ 0) (abs_iterState_lt_one hlam ω ζ 0)
            linarith
        _ = 60 * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    have hdrift : (T : ℝ) * ((320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ)) ≤
        (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
      have heq : (T : ℝ) * ((320 * lam * σ / γ) * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ)) =
          ((T : ℝ) * (320 * lam * σ / γ)) * ((n : ℝ) * (Fintype.card (KickBits T n) : ℝ)) := by ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_right hlam_drift (by positivity)).trans (by rw [one_mul])
    linarith [h1, hE_tele, hdrift]
  -- Markov on `BadEscape`.
  let Bad := Finset.univ.filter (fun ζ : KickBits T n =>
    ∀ s : Fin T,
      δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
        |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ) ∨
      δ₁ * (n : ℝ) ≤ ∑ v : Fin n,
        (iterState lam γ σ ω ζ (s.val + 1) v -
          iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2)
  have hmarkov : (Bad.card : ℝ) * ((T : ℝ) * min c_esc (5 * δ₁) * (n : ℝ)) ≤
      61 * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := by
    calc (Bad.card : ℝ) * ((T : ℝ) * min c_esc (5 * δ₁) * (n : ℝ))
        = ∑ _ζ ∈ Bad, ((T : ℝ) * min c_esc (5 * δ₁) * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ζ ∈ Bad, ∑ s : Fin T,
            (5 * ∑ v : Fin n,
              (iterState lam γ σ ω ζ (s.val + 1) v -
                iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 +
            if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
                |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ)
              then c_esc * (n : ℝ) else 0) := by
          refine Finset.sum_le_sum fun ζ hζ => ?_
          have hbad := (Finset.mem_filter.mp hζ).2
          calc (T : ℝ) * min c_esc (5 * δ₁) * (n : ℝ)
              = ∑ _s : Fin T, (min c_esc (5 * δ₁) * (n : ℝ)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
            _ ≤ _ := Finset.sum_le_sum fun s _ => by
                have hnn1 : 0 ≤ 5 * ∑ v : Fin n,
                    (iterState lam γ σ ω ζ (s.val + 1) v -
                      iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 :=
                  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
                rcases hbad s with h1 | h2
                · rw [if_pos h1]
                  have hle : min c_esc (5 * δ₁) * (n : ℝ) ≤ c_esc * (n : ℝ) :=
                    mul_le_mul_of_nonneg_right (min_le_left _ _) hn_pos.le
                  linarith
                · have hnn2 : 0 ≤ (if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
                      |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ) then c_esc * (n : ℝ) else 0) := by
                    split_ifs <;> positivity
                  have hle : min c_esc (5 * δ₁) * (n : ℝ) ≤ 5 * δ₁ * (n : ℝ) :=
                    mul_le_mul_of_nonneg_right (min_le_right _ _) hn_pos.le
                  linarith
      _ ≤ ∑ ζ : KickBits T n, ∑ s : Fin T,
            (5 * ∑ v : Fin n,
              (iterState lam γ σ ω ζ (s.val + 1) v -
                iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 +
            if δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
                |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ)
              then c_esc * (n : ℝ) else 0) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Finset.sum_nonneg fun _ _ =>
            add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
              (by split_ifs <;> positivity)
      _ ≤ 61 * (n : ℝ) * (Fintype.card (KickBits T n) : ℝ) := htot
  have hden_pos : 0 < (T : ℝ) * min c_esc (5 * δ₁) := mul_pos hT_pos hmin_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hden_pos]
  nlinarith only [hmarkov, hn_pos]

end KickEscape


/- ### Section 6: Deterministic Rounding, Fixed-`ε` Theorem, and `OMA.solution` -/

section RoundingAndMain

/-- Deterministic rounding: on a typical graph (`G_op` and `G_anti`), any nearly-integral,
nearly-stationary, nearly-balanced iterate rounds to an exact bisection with `≥ (1 - ε) n`
strictly friendly vertices. -/
lemma round_to_friendly_bisection {n : ℕ} (hn : 16 ≤ n)
    {ε γ δ δ₁ c_anti lam : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hγ0 : 0 < γ) (hγ_le : γ ≤ 1 / 16)
    (hδ0 : 0 < δ) (_hδ₁0 : 0 < δ₁) (hc0 : 0 < c_anti) (hlam : 0 < lam)
    (hγ_small : 400 * (12 * δ + 13 * γ) ≤ (ε / 8) * (c_anti / 2) ^ 2)
    (hδγ_eps : 3 * δ + 2 * γ ≤ ε / 8)
    (hδ₁_small : δ₁ ≤ (ε / 8) * (min (1 / 4) (c_anti / 40)) ^ 2)
    (hn_γ : 4 ≤ γ * (n : ℝ))
    (_hn_ε : 16 ≤ ε * (n : ℝ))
    (hn_c : 2 ≤ c_anti * Real.sqrt (n : ℝ))
    (ω : EdgeIdx n → Bool)
    (hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
      |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ))
    (hanti : ∀ s : Finset (Fin n),
      ((Finset.univ.filter (fun v : Fin n =>
        |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
          c_anti * Real.sqrt (n : ℝ))).card : ℝ) < (ε / 4) * (n : ℝ))
    (x xt x' : Fin n → ℝ)
    (_hx_lt : ∀ v, |x v| < 1)
    (hxt_lt : ∀ v, |xt v| < 1)
    (hxt_close : ∀ v, |xt v - x v| ≤ γ / 4)
    (hx'_eq : ∀ v, x' v = psi lam (xt v + (1 / 20 : ℝ) * iterGrad ω xt v))
    (hI : ((Finset.univ.filter (fun v : Fin n => |x v| ≤ 1 - γ)).card : ℝ) < δ * (n : ℝ))
    (hstep : ∑ v : Fin n, (x' v - xt v) ^ 2 < δ₁ * (n : ℝ))
    (hmean : |(∑ v : Fin n, x v) / (n : ℝ)| ≤ δ) :
    ∃ s : Finset (Fin n), s.card = n / 2 ∧
      (1 - ε) * (n : ℝ) ≤ (Green91.numFriendly ((graphEquiv n).symm ω) s : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let I : Finset (Fin n) := Finset.univ.filter (fun v => |x v| ≤ 1 - γ)
  let s₀ : Finset (Fin n) := Finset.univ.filter (fun v => 0 < xt v)
  let σ₀ : Fin n → ℝ := fun v => if v ∈ s₀ then 1 else -1
  -- Step 1: for `v ∉ I`, `σ₀ v` and `xt v` have the same sign and differ by `≤ 2 γ`.
  have houter : ∀ v : Fin n, v ∉ I →
      (0 < xt v → 1 - (5 / 4) * γ < xt v) ∧
      (¬ 0 < xt v → xt v < -(1 - (5 / 4) * γ)) ∧
      |σ₀ v - xt v| ≤ 2 * γ := by
    intro v hv
    have hgt : 1 - γ < |x v| := by
      by_contra hle
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hle⟩)
    have hclose := abs_le.mp (hxt_close v)
    have hxt_b := abs_lt.mp (hxt_lt v)
    rcases lt_or_ge 0 (x v) with hxpos | hxneg
    · rw [abs_of_pos hxpos] at hgt
      have hxt_hi : 1 - (5 / 4) * γ < xt v := by linarith
      have hxt_pos : 0 < xt v := by linarith
      have hv_s0 : v ∈ s₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt_pos⟩
      refine ⟨fun _ => hxt_hi, fun h => absurd hxt_pos h, ?_⟩
      simp only [σ₀, if_pos hv_s0]
      rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonpos hxneg] at hgt
      have hxt_lo : xt v < -(1 - (5 / 4) * γ) := by linarith
      have hxt_neg : ¬ 0 < xt v := by linarith
      have hv_s0 : v ∉ s₀ := fun h => hxt_neg (Finset.mem_filter.mp h).2
      refine ⟨fun h => absurd h hxt_neg, fun _ => hxt_lo, ?_⟩
      simp only [σ₀, if_neg hv_s0]
      rw [abs_of_neg (by linarith)]; linarith
  -- Step 2: balance bound `|s₀.card - n/2| ≤ (3/2)*(δ + γ) n + 1`.
  have hs0_bal : |(s₀.card : ℝ) - ((n / 2 : ℕ) : ℝ)| ≤ (3 / 2 * δ + 3 / 2 * γ) * (n : ℝ) + 1 := by
    have hL1_1 : ∑ v : Fin n, |σ₀ v - xt v| ≤ (2 * δ + 2 * γ) * (n : ℝ) := by
      have hpw : ∀ v : Fin n, |σ₀ v - xt v| ≤ (if v ∈ I then (2 : ℝ) else 0) + 2 * γ := by
        intro v
        by_cases hv : v ∈ I
        · rw [if_pos hv]
          have h1 : |σ₀ v| = 1 := by simp only [σ₀]; split_ifs <;> norm_num
          have h2 := (hxt_lt v).le
          have htri := abs_sub (σ₀ v) (xt v)
          linarith
        · rw [if_neg hv, zero_add]; exact (houter v hv).2.2
      calc ∑ v : Fin n, |σ₀ v - xt v|
          ≤ ∑ v : Fin n, ((if v ∈ I then (2 : ℝ) else 0) + 2 * γ) := Finset.sum_le_sum fun v _ => hpw v
        _ = 2 * (I.card : ℝ) + (2 * γ) * (n : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
              nsmul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ (2 * δ + 2 * γ) * (n : ℝ) := by linarith [hI]
    have hL1_2 : ∑ v : Fin n, |xt v - x v| ≤ γ * (n : ℝ) := by
      calc _ ≤ ∑ _v : Fin n, (γ / 4) := Finset.sum_le_sum fun v _ => hxt_close v
        _ = (γ / 4) * (n : ℝ) := by simp [mul_comm]
        _ ≤ γ * (n : ℝ) := by nlinarith [hγ0, hn_pos]
    have hsum_x : |∑ v : Fin n, x v| ≤ δ * (n : ℝ) := by
      rw [abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos] at hmean
      exact hmean
    have hsum_σ0 : |∑ v : Fin n, σ₀ v| ≤ (3 * δ + 3 * γ) * (n : ℝ) := by
      have heq : ∑ v : Fin n, σ₀ v =
          (∑ v : Fin n, x v) + (∑ v : Fin n, (xt v - x v)) + (∑ v : Fin n, (σ₀ v - xt v)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => by ring
      rw [heq]
      have h1 := abs_add_le ((∑ v : Fin n, x v) + ∑ v : Fin n, (xt v - x v)) (∑ v : Fin n, (σ₀ v - xt v))
      have h2 := abs_add_le (∑ v : Fin n, x v) (∑ v : Fin n, (xt v - x v))
      have h3 := Finset.abs_sum_le_sum_abs (fun v => xt v - x v) Finset.univ
      have h4 := Finset.abs_sum_le_sum_abs (fun v => σ₀ v - xt v) Finset.univ
      linarith [h1, h2, h3, h4, hsum_x, hL1_1, hL1_2]
    have hcard_eq : ∑ v : Fin n, σ₀ v = 2 * (s₀.card : ℝ) - (n : ℝ) := by
      have h1 : ∑ v : Fin n, σ₀ v = (∑ v : Fin n, if v ∈ s₀ then (2 : ℝ) else 0) - ∑ _v : Fin n, (1 : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => by simp only [σ₀]; split_ifs <;> ring
      rw [h1, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; ring
    have hhalf_bd : |(n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ)| ≤ 1 := by
      have h1 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      have h2 : n ≤ 2 * (n / 2) + 1 := by omega
      have h1R : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have h2R : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
      rw [abs_le]; constructor <;> linarith
    have hdiff2 : 2 * ((s₀.card : ℝ) - ((n / 2 : ℕ) : ℝ)) =
        (∑ v : Fin n, σ₀ v) + ((n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ)) := by linarith [hcard_eq]
    have h2abs : 2 * |(s₀.card : ℝ) - ((n / 2 : ℕ) : ℝ)| ≤ (3 * δ + 3 * γ) * (n : ℝ) + 1 := by
      have h1 := congrArg abs hdiff2
      rw [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)] at h1
      have htri := abs_add_le (∑ v : Fin n, σ₀ v) ((n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ))
      linarith [h1, htri, hsum_σ0, hhalf_bd]
    linarith
  -- Step 3: adjust `s₀` to an exact bisection `s` (`s.card = n / 2`) changing `S_diff`.
  have hex_bis : ∃ (s S_diff : Finset (Fin n)), s.card = n / 2 ∧
      (S_diff.card : ℝ) ≤ (2 * δ + 2 * γ) * (n : ℝ) + 1 ∧
      ∀ v : Fin n, v ∉ S_diff → (v ∈ s ↔ v ∈ s₀) := by
    rcases le_or_gt (n / 2) s₀.card with hge | hlt
    · obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hge
      refine ⟨s, s₀ \ s, hs_card, ?_, fun v hv => ?_⟩
      · have hc : ((s₀ \ s).card : ℝ) = (s₀.card : ℝ) - ((n / 2 : ℕ) : ℝ) := by
          have hsub_add := Finset.card_sdiff_add_card_eq_card hs_sub
          have hsub_nat : (s₀ \ s).card = s₀.card - n / 2 := by omega
          rw [hsub_nat, Nat.cast_sub hge]
        have hle := (abs_le.mp hs0_bal).2
        linarith [hc, hle, hδ0, hγ0, hn_pos]
      · constructor
        · intro h; exact hs_sub h
        · intro h; by_contra hns; exact hv (Finset.mem_sdiff.mpr ⟨h, hns⟩)
    · have hcompl_ge : n / 2 - s₀.card ≤ (Finset.univ \ s₀).card := by
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s₀)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        omega
      obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq hcompl_ge
      have hdisj : Disjoint s₀ A := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        exact (Finset.mem_sdiff.mp (hA_sub hv2)).2 hv1
      refine ⟨s₀ ∪ A, A, ?_, ?_, fun v hv => ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hA_card]; omega
      · have hc : (A.card : ℝ) = ((n / 2 : ℕ) : ℝ) - (s₀.card : ℝ) := by
          rw [hA_card, Nat.cast_sub hlt.le]
        have hle := (abs_le.mp hs0_bal).1
        linarith [hc, hle, hδ0, hγ0, hn_pos]
      · simp [hv]
  obtain ⟨s, S_diff, hs_card, hSdiff_card, hSdiff_agree⟩ := hex_bis
  refine ⟨s, hs_card, ?_⟩
  let σ : Fin n → ℝ := fun v => if v ∈ s then 1 else -1
  -- Step 4: `‖σ - xt‖_2^2 ≤ (12 δ + 13 γ) n`, transferred through `hop` to `iterGrad`.
  have hL2_diff : ∑ v : Fin n, (σ v - xt v) ^ 2 ≤ (12 * δ + 13 * γ) * (n : ℝ) := by
    have hpw : ∀ v : Fin n, (σ v - xt v) ^ 2 ≤
        (if v ∈ S_diff then (4 : ℝ) else 0) + (if v ∈ I then (4 : ℝ) else 0) + 4 * γ := by
      intro v
      by_cases h1 : v ∈ S_diff
      · rw [if_pos h1]
        have hσ1 : |σ v| = 1 := by simp only [σ]; split_ifs <;> norm_num
        have htri := abs_sub (σ v) (xt v)
        have h2 : |σ v - xt v| ≤ 2 := by linarith [htri, hσ1, hxt_lt v]
        have hsq := pow_le_pow_left₀ (abs_nonneg _) h2 2
        rw [sq_abs] at hsq
        have hnn : 0 ≤ (if v ∈ I then (4 : ℝ) else 0) + 4 * γ := by split_ifs <;> positivity
        linarith
      · by_cases h2 : v ∈ I
        · rw [if_neg h1, if_pos h2]
          have hσ1 : |σ v| = 1 := by simp only [σ]; split_ifs <;> norm_num
          have htri := abs_sub (σ v) (xt v)
          have h3 : |σ v - xt v| ≤ 2 := by linarith [htri, hσ1, hxt_lt v]
          have hsq := pow_le_pow_left₀ (abs_nonneg _) h3 2
          rw [sq_abs] at hsq
          linarith [hγ0]
        · rw [if_neg h1, if_neg h2, zero_add, zero_add]
          have heq : σ v = σ₀ v := by simp only [σ, σ₀, hSdiff_agree v h1]
          rw [heq]
          have hle := (houter v h2).2.2
          have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
          rw [sq_abs] at hsq
          nlinarith [hsq, hγ0, hγ_le]
    calc ∑ v : Fin n, (σ v - xt v) ^ 2
        ≤ ∑ v : Fin n, ((if v ∈ S_diff then (4 : ℝ) else 0) + (if v ∈ I then (4 : ℝ) else 0) + 4 * γ) :=
          Finset.sum_le_sum fun v _ => hpw v
      _ = 4 * (S_diff.card : ℝ) + 4 * (I.card : ℝ) + 4 * γ * (n : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 4 * ((2 * δ + 2 * γ) * (n : ℝ) + 1) + 4 * (δ * (n : ℝ)) + 4 * γ * (n : ℝ) := by
          linarith [hSdiff_card, hI]
      _ ≤ (12 * δ + 13 * γ) * (n : ℝ) := by linarith [hn_γ]
  have hgrad_L2 : ∑ v : Fin n, (iterGrad ω σ v - iterGrad ω xt v) ^ 2 ≤
      400 * (12 * δ + 13 * γ) * (n : ℝ) := by
    have hlin : ∀ v : Fin n, iterGrad ω σ v - iterGrad ω xt v = iterGrad ω (fun w => σ w - xt w) v := by
      intro v; simp only [iterGrad, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun w _ => by ring
    simp_rw [hlin]
    have hm := op_norm_matvec_sq (by omega : 1 ≤ n) ω (by norm_num : (0 : ℝ) ≤ 20) hop (fun w => σ w - xt w)
    calc _ ≤ (20 : ℝ) ^ 2 * ∑ w : Fin n, (σ w - xt w) ^ 2 := hm
      _ ≤ (20 : ℝ) ^ 2 * ((12 * δ + 13 * γ) * (n : ℝ)) := mul_le_mul_of_nonneg_left hL2_diff (by norm_num)
      _ = 400 * (12 * δ + 13 * γ) * (n : ℝ) := by ring
  -- Step 5: define the 5 bad vertex sets and bound their total cardinality `< ε * n`.
  let θ_step : ℝ := min (1 / 4) (c_anti / 40)
  have hθ_pos : 0 < θ_step := lt_min (by norm_num) (by positivity)
  let B_step : Finset (Fin n) := Finset.univ.filter (fun v => θ_step < |x' v - xt v|)
  let B_grad : Finset (Fin n) := Finset.univ.filter (fun v => c_anti / 2 < |iterGrad ω σ v - iterGrad ω xt v|)
  let B_anti : Finset (Fin n) := Finset.univ.filter (fun v =>
    |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤ c_anti * Real.sqrt (n : ℝ))
  have hBstep_card : (B_step.card : ℝ) ≤ (ε / 8) * (n : ℝ) := by
    have hmark : (B_step.card : ℝ) * θ_step ^ 2 ≤ ∑ v : Fin n, (x' v - xt v) ^ 2 := by
      calc (B_step.card : ℝ) * θ_step ^ 2 = ∑ _v ∈ B_step, θ_step ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ B_step, (x' v - xt v) ^ 2 := Finset.sum_le_sum fun v hv => by
            have hgt := (Finset.mem_filter.mp hv).2
            have h2 := pow_le_pow_left₀ hθ_pos.le hgt.le 2
            rwa [sq_abs] at h2
        _ ≤ ∑ v : Fin n, (x' v - xt v) ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    have hlt : (B_step.card : ℝ) * θ_step ^ 2 ≤ ((ε / 8) * (n : ℝ)) * θ_step ^ 2 := by
      calc _ ≤ δ₁ * (n : ℝ) := hmark.trans hstep.le
        _ ≤ ((ε / 8) * θ_step ^ 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hδ₁_small hn_pos.le
        _ = ((ε / 8) * (n : ℝ)) * θ_step ^ 2 := by ring
    exact le_of_mul_le_mul_right hlt (sq_pos_of_pos hθ_pos)
  have hBgrad_card : (B_grad.card : ℝ) ≤ (ε / 8) * (n : ℝ) := by
    have hmark : (B_grad.card : ℝ) * (c_anti / 2) ^ 2 ≤ ∑ v : Fin n, (iterGrad ω σ v - iterGrad ω xt v) ^ 2 := by
      calc (B_grad.card : ℝ) * (c_anti / 2) ^ 2 = ∑ _v ∈ B_grad, (c_anti / 2) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ B_grad, (iterGrad ω σ v - iterGrad ω xt v) ^ 2 := Finset.sum_le_sum fun v hv => by
            have hgt := (Finset.mem_filter.mp hv).2
            have h2 := pow_le_pow_left₀ (by positivity) hgt.le 2
            rwa [sq_abs] at h2
        _ ≤ ∑ v : Fin n, (iterGrad ω σ v - iterGrad ω xt v) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    have hle : (B_grad.card : ℝ) * (c_anti / 2) ^ 2 ≤ ((ε / 8) * (n : ℝ)) * (c_anti / 2) ^ 2 := by
      calc _ ≤ 400 * (12 * δ + 13 * γ) * (n : ℝ) := hmark.trans hgrad_L2
        _ ≤ ((ε / 8) * (c_anti / 2) ^ 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hγ_small hn_pos.le
        _ = ((ε / 8) * (n : ℝ)) * (c_anti / 2) ^ 2 := by ring
    exact le_of_mul_le_mul_right hle (sq_pos_of_pos (by positivity))
  let BadAll : Finset (Fin n) := I ∪ S_diff ∪ B_step ∪ B_grad ∪ B_anti
  have hBadAll_card : (BadAll.card : ℝ) ≤ ε * (n : ℝ) := by
    have hu : (BadAll.card : ℝ) ≤ (I.card : ℝ) + (S_diff.card : ℝ) + (B_step.card : ℝ) +
        (B_grad.card : ℝ) + (B_anti.card : ℝ) := by
      have h1 : BadAll.card ≤ I.card + S_diff.card + B_step.card + B_grad.card + B_anti.card := by
        calc BadAll.card
            ≤ (I ∪ S_diff ∪ B_step ∪ B_grad).card + B_anti.card := Finset.card_union_le _ _
          _ ≤ (I ∪ S_diff ∪ B_step).card + B_grad.card + B_anti.card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ (I ∪ S_diff).card + B_step.card + B_grad.card + B_anti.card :=
              Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
          _ ≤ I.card + S_diff.card + B_step.card + B_grad.card + B_anti.card :=
              Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
      exact_mod_cast h1
    have hanti_s := hanti s
    have hδγ_mul : (3 * δ + 2 * γ) * (n : ℝ) ≤ (ε / 8) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hδγ_eps hn_pos.le
    linarith [hu, hI, hSdiff_card, hBstep_card, hBgrad_card, hanti_s, hδγ_mul]
  -- Step 6: every `v ∉ BadAll` is strictly friendly (`0 < friendliness G s v`).
  have hgood_friendly : ∀ v : Fin n, v ∉ BadAll →
      0 < Green91.friendliness ((graphEquiv n).symm ω) s v := by
    intro v hv
    have hvI : v ∉ I := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hvS : v ∉ S_diff := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
    have hvSt : v ∉ B_step := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ h)))
    have hvG : v ∉ B_grad := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvA : v ∉ B_anti := fun h => hv (Finset.mem_union_right _ h)
    have hstep_le : |x' v - xt v| ≤ θ_step := not_lt.mp fun h => hvSt (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hgrad_le : |iterGrad ω σ v - iterGrad ω xt v| ≤ c_anti / 2 :=
      not_lt.mp fun h => hvG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hanti_gt : c_anti * Real.sqrt (n : ℝ) < |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| :=
      not_le.mp fun h => hvA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hinv_eq : hInv lam (x' v) = xt v + (1 / 20 : ℝ) * iterGrad ω xt v := by
      rw [hx'_eq v, hInv_psi hlam]
    have hx'_lt : |x' v| < 1 := by rw [hx'_eq v]; exact abs_psi_lt_one hlam _
    have hθ_14 : θ_step ≤ 1 / 4 := min_le_left _ _
    have hθ_c : 20 * θ_step ≤ c_anti / 2 := by
      have := min_le_right (1 / 4) (c_anti / 40); linarith
    have hσ_yxt : -c_anti / 2 ≤ σ v * iterGrad ω xt v := by
      have heqσ : σ v = σ₀ v := by simp only [σ, σ₀, hSdiff_agree v hvS]
      rw [heqσ]
      by_cases hpos : 0 < xt v
      · have hvs0 : v ∈ s₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
        simp only [σ₀, if_pos hvs0, one_mul]
        have hxt_hi := (houter v hvI).1 hpos
        have hx'_pos : 0 < x' v := by
          have := (abs_le.mp hstep_le).1
          linarith [hxt_hi, hθ_14, hγ_le]
        have hinv_gt : x' v < hInv lam (x' v) := by
          have := hInv_sub_pos hlam hx'_pos (abs_lt.mp hx'_lt).2
          linarith
        have h1 := (abs_le.mp hstep_le).1
        linarith [hinv_eq, hinv_gt, h1, hθ_c]
      · have hvs0 : v ∉ s₀ := fun h => hpos (Finset.mem_filter.mp h).2
        simp only [σ₀, if_neg hvs0]
        have hxt_lo := (houter v hvI).2.1 hpos
        have hx'_neg : x' v < 0 := by
          have := (abs_le.mp hstep_le).2
          linarith [hxt_lo, hθ_14, hγ_le]
        have hinv_lt : hInv lam (x' v) < x' v := by
          have := hInv_sub_neg hlam (abs_lt.mp hx'_lt).1 hx'_neg
          linarith
        have h2 := (abs_le.mp hstep_le).2
        linarith [hinv_eq, hinv_lt, h2, hθ_c]
    have hσ_yσ : -c_anti ≤ σ v * iterGrad ω σ v := by
      have hdiff : |σ v * iterGrad ω σ v - σ v * iterGrad ω xt v| ≤ c_anti / 2 := by
        rw [← mul_sub, abs_mul]
        have hσ1 : |σ v| = 1 := by simp only [σ]; split_ifs <;> norm_num
        rw [hσ1, one_mul]; exact hgrad_le
      have h1 := (abs_le.mp hdiff).1
      linarith [hσ_yxt, h1]
    have hsum_A : -(c_anti * Real.sqrt (n : ℝ)) ≤ σ v * (∑ w : Fin n, adjSign ω v w * σ w) := by
      have h1 : σ v * iterGrad ω σ v = (σ v * (∑ w : Fin n, adjSign ω v w * σ w)) / Real.sqrt (n : ℝ) := by
        simp only [iterGrad]; ring
      rw [h1, le_div_iff₀ hsq_pos] at hσ_yσ
      linarith
    have hsum_σ : |∑ w : Fin n, σ w| ≤ 1 := by
      have h1 : ∑ w : Fin n, σ w = 2 * ((n / 2 : ℕ) : ℝ) - (n : ℝ) := by
        have h2 : ∑ w : Fin n, σ w = (∑ w : Fin n, if w ∈ s then (2 : ℝ) else 0) - ∑ _w : Fin n, (1 : ℝ) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun w _ => by simp only [σ]; split_ifs <;> ring
        rw [h2, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hs_card,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; ring
      rw [h1]
      have ha : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      have hb : n ≤ 2 * (n / 2) + 1 := by omega
      have haR : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha
      have hbR : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hb
      rw [abs_le]; constructor <;> linarith
    have hfr := friendliness_eq_adjSign ω s v
    have hσ_sum_bd : -(1 : ℝ) ≤ σ v * (∑ w : Fin n, σ w) := by
      have h1 : |σ v * (∑ w : Fin n, σ w)| ≤ 1 := by
        rw [abs_mul]
        have hσ1 : |σ v| = 1 := by simp only [σ]; split_ifs <;> norm_num
        rw [hσ1, one_mul]; exact hsum_σ
      exact (abs_le.mp h1).1
    have hfr_lo : -2 * (c_anti * Real.sqrt (n : ℝ)) ≤
        2 * (Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ) := by
      linarith [hfr, hsum_A, hσ_sum_bd, hn_c]
    by_contra hle
    have hleR : (Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ) ≤ 0 := by
      exact_mod_cast (not_lt.mp hle)
    rw [abs_of_nonpos hleR] at hanti_gt
    linarith [hfr_lo, hanti_gt]
  -- Count `numFriendly G s ≥ (univ \ BadAll).card ≥ (1 - ε) n`.
  have hsub : Finset.univ \ BadAll ⊆
      Finset.univ.filter (fun v : Fin n => 0 < Green91.friendliness ((graphEquiv n).symm ω) s v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood_friendly v (Finset.mem_sdiff.mp hv).2⟩
  have hnf_eq : Green91.numFriendly ((graphEquiv n).symm ω) s =
      (Finset.univ.filter (fun v : Fin n => 0 < Green91.friendliness ((graphEquiv n).symm ω) s v)).card := rfl
  have hcard_ge : (n : ℝ) - (BadAll.card : ℝ) ≤
      (Green91.numFriendly ((graphEquiv n).symm ω) s : ℝ) := by
    have h1 : (Finset.univ \ BadAll).card + BadAll.card = n := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ BadAll)
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have h2 : (Finset.univ \ BadAll).card ≤ Green91.numFriendly ((graphEquiv n).symm ω) s := by
      rw [hnf_eq]; exact Finset.card_le_card hsub
    have h1R : ((Finset.univ \ BadAll).card : ℝ) + (BadAll.card : ℝ) = (n : ℝ) := by exact_mod_cast h1
    have h2R : ((Finset.univ \ BadAll).card : ℝ) ≤ (Green91.numFriendly ((graphEquiv n).symm ω) s : ℝ) := by
      exact_mod_cast h2
    linarith
  linarith [hcard_ge, hBadAll_card]

lemma exp_n2_tail {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)) 4
  simp [Finset.sum_range_succ, Nat.factorial] at hsum
  have hexp_ge : (n : ℝ) ^ 3 ≤ Real.exp (2 * (n : ℝ)) := by
    have h1 : (2 * (n : ℝ)) ^ 3 / 6 = (4 / 3 : ℝ) * (n : ℝ) ^ 3 := by ring
    have h2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg hn_pos.le 3
    nlinarith only [hsum, h1, hn_pos, h2, h3]
  have hneg : Real.exp (-2 * (n : ℝ)) = (Real.exp (2 * (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hneg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hn_pos]
  linarith only [hexp_ge, show (n : ℝ) ^ 2 * (n : ℝ) = (n : ℝ) ^ 3 by ring]

lemma exp_tail_le {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith only [h]
  exact (le_mul_of_one_le_left (Real.exp_pos _).le h1).trans (exp_n2_tail hn)

lemma half_pow_le_inv {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hleR : (n : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  rw [one_div_pow, one_div_le_one_div (by positivity) hn_pos]
  exact hleR

lemma sqrt_ge_of_sq_div_le {a c n : ℝ} (_ha : 0 ≤ a) (hc : 0 < c) (hn : 0 < n)
    (h : a ^ 2 / c ^ 2 ≤ n) : a ≤ c * Real.sqrt n := by
  have h2 : a ^ 2 ≤ c ^ 2 * n := by
    have := (div_le_iff₀ (sq_pos_of_pos hc)).mp h
    linarith only [this, mul_comm n (c ^ 2)]
  have hsq : a ^ 2 ≤ (c * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]; exact h2
  have hpos : 0 ≤ c * Real.sqrt n := mul_nonneg hc.le (Real.sqrt_nonneg n)
  nlinarith only [hsq, _ha, hpos]

lemma bad_esc_card_le {T n : ℕ} (hn1 : 1 ≤ n) (hT1 : 1 ≤ T)
    {lam γ σ δ δ₁ p_fail : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 4)
    (hγ0 : 0 < γ) (hγ_le2 : γ ≤ 1 / 2) (hσ0 : 0 < σ) (hσ : σ ≤ γ / 8)
    (hδ0 : 0 < δ) (hδ₁0 : 0 < δ₁) (hp0 : 0 < p_fail)
    (hnδ : 2 ≤ δ * (n : ℝ))
    (hlam_grad : 16 * lam / γ ≤ (1 / 40) * σ * Real.sqrt (δ / 200))
    (hlam_drift : (T : ℝ) * (320 * lam * σ / γ) ≤ 1)
    (hT_ge : 122 / (p_fail * min (5 * δ * (δ ^ 2 / 600000) * (min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200))) ^ 2) (5 * δ₁)) ≤ (T : ℝ)) :
    let BadOp : Finset (EdgeIdx n → Bool) := Finset.univ.filter (fun ω =>
      ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
        20 * Real.sqrt (n : ℝ) < |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|)
    let BadEscP : Finset ((EdgeIdx n → Bool) × KickBits T n) :=
      Finset.univ.filter (fun p => p.1 ∉ BadOp ∧
        ∀ s : Fin T,
          δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
            |iterState lam γ σ p.1 p.2 s.val v| ≤ 1 - γ)).card : ℝ) ∨
          δ₁ * (n : ℝ) ≤ ∑ v : Fin n,
            (iterState lam γ σ p.1 p.2 (s.val + 1) v -
              iterKick γ σ p.2 s.val (iterState lam γ σ p.1 p.2 s.val) v) ^ 2)
    (BadEscP.card : ℝ) ≤
      (p_fail / 2) * ((Fintype.card (EdgeIdx n → Bool) : ℝ) * (Fintype.card (KickBits T n) : ℝ)) := by
  intro BadOp BadEscP
  set NE : ℝ := (Fintype.card (EdgeIdx n → Bool) : ℝ)
  set NK : ℝ := (Fintype.card (KickBits T n) : ℝ)
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNK_pos : 0 < NK := Nat.cast_pos.mpr Fintype.card_pos
  set d₀ : ℝ := min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200))
  set c_esc : ℝ := 5 * δ * (δ ^ 2 / 600000) * d₀ ^ 2
  have hd₀_pos : 0 < d₀ := lt_min (by positivity) (by positivity)
  have hcesc_pos : 0 < c_esc := by positivity
  have hmin_pos : 0 < min c_esc (5 * δ₁) := lt_min hcesc_pos (by positivity)
  have hsum : (BadEscP.card : ℝ) = ∑ ω : EdgeIdx n → Bool,
      if ω ∉ BadOp then
        ((Finset.univ.filter (fun ζ : KickBits T n =>
          ∀ s : Fin T,
            δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
              |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ) ∨
            δ₁ * (n : ℝ) ≤ ∑ v : Fin n,
              (iterState lam γ σ ω ζ (s.val + 1) v -
                iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2)).card : ℝ)
      else 0 := by
    have h1 : (BadEscP.card : ℝ) = ∑ p : (EdgeIdx n → Bool) × KickBits T n, if p ∈ BadEscP then (1 : ℝ) else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hnot : ω ∉ BadOp
    · rw [if_pos hnot, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun ζ _ => by simp [BadEscP, hnot]
    · rw [if_neg hnot]
      exact Finset.sum_eq_zero fun ζ _ => by simp [BadEscP, hnot]
  have h61 : 61 / ((T : ℝ) * min c_esc (5 * δ₁)) ≤ p_fail / 2 := by
    rw [div_le_div_iff₀ (mul_pos hT_pos hmin_pos) two_pos]
    have h1 := (div_le_iff₀ (mul_pos hp0 hmin_pos)).mp hT_ge
    have heq : p_fail * ((T : ℝ) * min c_esc (5 * δ₁)) = (T : ℝ) * (p_fail * min c_esc (5 * δ₁)) := by ring
    linarith only [h1, heq]
  rw [hsum]
  calc _ ≤ ∑ _ω : EdgeIdx n → Bool, ((p_fail / 2) * NK) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        by_cases hbad : ω ∈ BadOp
        · rw [if_neg (not_not.mpr hbad)]; positivity
        · rw [if_pos hbad]
          have hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
              |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ) := by
            intro x y hx hy; by_contra hgt
            exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, y, hx, hy, lt_of_not_ge hgt⟩⟩)
          have hpt := pointwise_good_step_prob hn1 hT1 hlam0 hlam1 hγ0 hγ_le2 hσ0 hσ hδ0 hδ₁0
            hnδ hlam_grad hlam_drift ω hop
          exact hpt.trans (mul_le_mul_of_nonneg_right h61 hNK_pos.le)
    _ = NE * ((p_fail / 2) * NK) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (p_fail / 2) * (NE * NK) := by ring

lemma bad_mean_card_le {T n : ℕ} (hn1 : 1 ≤ n)
    {lam γ σ δ p_fail : ℝ} (hlam0 : 0 < lam)
    (hγ0 : 0 < γ) (hγ_le2 : γ ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ γ / 8)
    (hδ0 : 0 < δ) (hp0 : 0 < p_fail)
    (hn_var : 10 * (T : ℝ) *
      (((T : ℝ) ^ 2 + 8 * (T : ℝ)) * (36 : ℝ) ^ T +
        2 * ((T : ℝ) + 1) * ((T : ℝ) * (6 : ℝ) ^ T * (64 : ℝ) ^ T * (1 + 100 / γ + 1 / Real.sqrt lam)) ^ 2 +
        8 * ((T : ℝ) + 1)) / (δ ^ 2 * p_fail) ≤ (n : ℝ)) :
    let BadMean : Fin T → Finset ((EdgeIdx n → Bool) × KickBits T n) := fun s =>
      Finset.univ.filter (fun p => δ < |(∑ v : Fin n, iterState lam γ σ p.1 p.2 s.val v) / (n : ℝ)|)
    ((Finset.univ.biUnion BadMean).card : ℝ) ≤
      (p_fail / 10) * ((Fintype.card (EdgeIdx n → Bool) : ℝ) * (Fintype.card (KickBits T n) : ℝ)) := by
  intro BadMean
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  set NE : ℝ := (Fintype.card (EdgeIdx n → Bool) : ℝ)
  set NK : ℝ := (Fintype.card (KickBits T n) : ℝ)
  have hNprod : (Fintype.card ((EdgeIdx n → Bool) × KickBits T n) : ℝ) = NE * NK := by simp [NE, NK]
  set C_rem_max : ℝ := (T : ℝ) * (6 : ℝ) ^ T * (64 : ℝ) ^ T * (1 + 100 / γ + 1 / Real.sqrt lam)
  set C_var_max : ℝ := ((T : ℝ) ^ 2 + 8 * (T : ℝ)) * (36 : ℝ) ^ T + 2 * ((T : ℝ) + 1) * C_rem_max ^ 2
  have hexp_n2 : (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) ≤ 1 / (n : ℝ) := exp_n2_tail hn1
  have hper_s : ∀ s : Fin T, ((BadMean s).card : ℝ) ≤
      ((C_var_max + 8 * ((T : ℝ) + 1)) / (δ ^ 2 * (n : ℝ))) * (NE * NK) := by
    intro s
    have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le s.val) s.isLt)
    have hvar := mean_iterState_var_le (T := T) hn1 hlam0 hγ0 hγ_le2 hσ0 hσ s.val
    have hmark : ((BadMean s).card : ℝ) * δ ^ 2 ≤
        ∑ p : (EdgeIdx n → Bool) × KickBits T n,
          ((∑ v : Fin n, iterState lam γ σ p.1 p.2 s.val v) / (n : ℝ)) ^ 2 := by
      calc ((BadMean s).card : ℝ) * δ ^ 2 = ∑ _p ∈ BadMean s, δ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ BadMean s, ((∑ v : Fin n, iterState lam γ σ p.1 p.2 s.val v) / (n : ℝ)) ^ 2 :=
            Finset.sum_le_sum fun p hp => by
              have hgt := (Finset.mem_filter.mp hp).2
              have h2 := pow_le_pow_left₀ hδ0.le hgt.le 2
              rwa [sq_abs] at h2
        _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    have hsle : (s.val : ℝ) ≤ (T : ℝ) := by exact_mod_cast s.isLt.le
    have hpow6 : (6 : ℝ) ^ s.val ≤ (6 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) s.isLt.le
    have hpow36 : (36 : ℝ) ^ s.val ≤ (36 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) s.isLt.le
    have hpow64 : (64 : ℝ) ^ s.val ≤ (64 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) s.isLt.le
    have hCrem_le : (s.val : ℝ) * (6 : ℝ) ^ s.val * (64 : ℝ) ^ s.val * (1 + 100 / γ + 1 / Real.sqrt lam) ≤
        C_rem_max := by
      have h1 : (s.val : ℝ) * (6 : ℝ) ^ s.val * (64 : ℝ) ^ s.val ≤ (T : ℝ) * (6 : ℝ) ^ T * (64 : ℝ) ^ T :=
        mul_le_mul (mul_le_mul hsle hpow6 (by positivity) hT_pos.le) hpow64 (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hCvar_le : (((s.val : ℝ) ^ 2 + 8 * (s.val : ℝ)) * (36 : ℝ) ^ s.val +
        2 * ((s.val : ℝ) + 1) *
          ((s.val : ℝ) * (6 : ℝ) ^ s.val * (64 : ℝ) ^ s.val * (1 + 100 / γ + 1 / Real.sqrt lam)) ^ 2) ≤
        C_var_max := by
      have ha : ((s.val : ℝ) ^ 2 + 8 * (s.val : ℝ)) * (36 : ℝ) ^ s.val ≤
          ((T : ℝ) ^ 2 + 8 * (T : ℝ)) * (36 : ℝ) ^ T :=
        mul_le_mul (by nlinarith only [hsle, Nat.cast_nonneg (α := ℝ) s.val]) hpow36 (by positivity) (by positivity)
      have hb : 2 * ((s.val : ℝ) + 1) *
          ((s.val : ℝ) * (6 : ℝ) ^ s.val * (64 : ℝ) ^ s.val * (1 + 100 / γ + 1 / Real.sqrt lam)) ^ 2 ≤
          2 * ((T : ℝ) + 1) * C_rem_max ^ 2 :=
        mul_le_mul (by linarith only [hsle]) (pow_le_pow_left₀ (by positivity) hCrem_le 2) (by positivity) (by positivity)
      exact add_le_add ha hb
    have htail : 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) ≤
        8 * ((T : ℝ) + 1) / (n : ℝ) := by
      have heq : 8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) =
          8 * ((T : ℝ) + 1) * ((n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ))) := by ring
      rw [heq, ← mul_one_div]
      exact mul_le_mul_of_nonneg_left hexp_n2 (by positivity)
    have hcomb := hmark.trans hvar
    rw [hNprod] at hcomb
    have hle_rhs : (((s.val : ℝ) ^ 2 + 8 * (s.val : ℝ)) * (36 : ℝ) ^ s.val +
        2 * ((s.val : ℝ) + 1) *
          ((s.val : ℝ) * (6 : ℝ) ^ s.val * (64 : ℝ) ^ s.val * (1 + 100 / γ + 1 / Real.sqrt lam)) ^ 2) / (n : ℝ) +
        8 * ((T : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ)) ≤
        (C_var_max + 8 * ((T : ℝ) + 1)) / (n : ℝ) := by
      conv_rhs => rw [add_div]
      exact add_le_add (div_le_div_of_nonneg_right hCvar_le hn_pos.le) htail
    have hfin : ((BadMean s).card : ℝ) * δ ^ 2 ≤
        ((C_var_max + 8 * ((T : ℝ) + 1)) / (n : ℝ)) * (NE * NK) :=
      hcomb.trans (mul_le_mul_of_nonneg_right hle_rhs (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (sq_pos_of_pos hδ0) hn_pos)]
    have heq : ((BadMean s).card : ℝ) * (δ ^ 2 * (n : ℝ)) = (((BadMean s).card : ℝ) * δ ^ 2) * (n : ℝ) := by ring
    rw [heq]
    calc (((BadMean s).card : ℝ) * δ ^ 2) * (n : ℝ)
        ≤ (((C_var_max + 8 * ((T : ℝ) + 1)) / (n : ℝ)) * (NE * NK)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hfin hn_pos.le
      _ = (C_var_max + 8 * ((T : ℝ) + 1)) * (NE * NK) := by field_simp
  have hbi : ((Finset.univ.biUnion BadMean).card : ℝ) ≤ ∑ s : Fin T, ((BadMean s).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc ((Finset.univ.biUnion BadMean).card : ℝ)
      ≤ ∑ s : Fin T, ((BadMean s).card : ℝ) := hbi
    _ ≤ ∑ _s : Fin T, (((C_var_max + 8 * ((T : ℝ) + 1)) / (δ ^ 2 * (n : ℝ))) * (NE * NK)) :=
        Finset.sum_le_sum fun s _ => hper_s s
    _ = ((T : ℝ) * (C_var_max + 8 * ((T : ℝ) + 1)) / (δ ^ 2 * (n : ℝ))) * (NE * NK) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (p_fail / 10) * (NE * NK) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hδ0) hn_pos) (by norm_num)]
        have h1 := (div_le_iff₀ (mul_pos (sq_pos_of_pos hδ0) hp0)).mp hn_var
        have heq1 : (T : ℝ) * (C_var_max + 8 * ((T : ℝ) + 1)) * 10 =
            10 * (T : ℝ) * (C_var_max + 8 * ((T : ℝ) + 1)) := by ring
        have heq2 : p_fail * (δ ^ 2 * (n : ℝ)) = (n : ℝ) * (δ ^ 2 * p_fail) := by ring
        linarith only [h1, heq1, heq2]

/-- Single-`n` probability lower bound given opaque parameters (avoids deep `let`-unfolding in `whnf`). -/
lemma fixed_eps_single_n {T n : ℕ} (hn16 : 16 ≤ n) (hT1 : 1 ≤ T)
    {ε p_fail c_anti γ δ σ δ₁ lam : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hp0 : 0 < p_fail) (hc0 : 0 < c_anti)
    (hγ0 : 0 < γ) (hγ_le16 : γ ≤ 1 / 16) (hδ0 : 0 < δ) (hσ0 : 0 < σ) (hσ : σ ≤ γ / 8)
    (hδ₁0 : 0 < δ₁) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 4)
    (hγ_small : 400 * (12 * δ + 13 * γ) ≤ (ε / 8) * (c_anti / 2) ^ 2)
    (hδγ_eps : 3 * δ + 2 * γ ≤ ε / 8)
    (hδ₁_small : δ₁ ≤ (ε / 8) * (min (1 / 4) (c_anti / 40)) ^ 2)
    (hlam_grad : 16 * lam / γ ≤ (1 / 40) * σ * Real.sqrt (δ / 200))
    (hlam_drift : (T : ℝ) * (320 * lam * σ / γ) ≤ 1)
    (hT_ge : 122 / (p_fail * min (5 * δ * (δ ^ 2 / 600000) * (min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200))) ^ 2) (5 * δ₁)) ≤ (T : ℝ))
    (hn_γ : 4 ≤ γ * (n : ℝ)) (hn_δ : 2 ≤ δ * (n : ℝ)) (hn_ε : 16 ≤ ε * (n : ℝ))
    (hn_c : 2 ≤ c_anti * Real.sqrt (n : ℝ))
    (hn_anti : 6 * c_anti + 4 / Real.sqrt (n : ℝ) ≤ (1 / 8 : ℝ) ^ (Nat.ceil (1 / (ε / 4))))
    (hn_p : 20 / p_fail ≤ (n : ℝ))
    (hn_var : 10 * (T : ℝ) *
      (((T : ℝ) ^ 2 + 8 * (T : ℝ)) * (36 : ℝ) ^ T +
        2 * ((T : ℝ) + 1) * ((T : ℝ) * (6 : ℝ) ^ T * (64 : ℝ) ^ T * (1 + 100 / γ + 1 / Real.sqrt lam)) ^ 2 +
        8 * ((T : ℝ) + 1)) / (δ ^ 2 * p_fail) ≤ (n : ℝ)) :
    1 - ENNReal.ofReal p_fail ≤ Green91.prob n fun G =>
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (1 - ε) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hγ_le2 : γ ≤ 1 / 2 := hγ_le16.trans (by norm_num)
  have hexp_le : Real.exp (-2 * (n : ℝ)) ≤ 1 / (n : ℝ) := exp_tail_le hn1
  have hhalf_le : (1 / 2 : ℝ) ^ n ≤ 1 / (n : ℝ) := half_pow_le_inv hn1
  let P : SimpleGraph (Fin n) → Prop := fun G =>
    ∃ s : Finset (Fin n), s.card = n / 2 ∧
      (1 - ε) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ)
  let FailG : Finset (EdgeIdx n → Bool) := Finset.univ.filter (fun ω => ¬ P ((graphEquiv n).symm ω))
  let BadOp : Finset (EdgeIdx n → Bool) := Finset.univ.filter (fun ω =>
    ∃ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) ∧ (∑ i, (y i) ^ 2 ≤ 1) ∧
      20 * Real.sqrt (n : ℝ) < |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j|)
  let BadAnti : Finset (EdgeIdx n → Bool) := Finset.univ.filter (fun ω =>
    ∃ s : Finset (Fin n), (ε / 4) * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
      |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤ c_anti * Real.sqrt (n : ℝ))).card : ℝ))
  let BadEscP : Finset ((EdgeIdx n → Bool) × KickBits T n) :=
    Finset.univ.filter (fun p => p.1 ∉ BadOp ∧
      ∀ s : Fin T,
        δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |iterState lam γ σ p.1 p.2 s.val v| ≤ 1 - γ)).card : ℝ) ∨
        δ₁ * (n : ℝ) ≤ ∑ v : Fin n,
          (iterState lam γ σ p.1 p.2 (s.val + 1) v -
            iterKick γ σ p.2 s.val (iterState lam γ σ p.1 p.2 s.val) v) ^ 2)
  let BadMean : Fin T → Finset ((EdgeIdx n → Bool) × KickBits T n) := fun s =>
    Finset.univ.filter (fun p => δ < |(∑ v : Fin n, iterState lam γ σ p.1 p.2 s.val v) / (n : ℝ)|)
  have hcov : FailG ×ˢ (Finset.univ : Finset (KickBits T n)) ⊆
      (BadOp ×ˢ Finset.univ) ∪ (BadAnti ×ˢ Finset.univ) ∪ BadEscP ∪
      Finset.univ.biUnion BadMean := by
    intro ⟨ω, ζ⟩ hmem
    have hfail : ¬ P ((graphEquiv n).symm ω) := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2
    by_cases h1 : ω ∈ BadOp
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨h1, Finset.mem_univ _⟩)))
    by_cases h2 : ω ∈ BadAnti
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨h2, Finset.mem_univ _⟩)))
    by_cases h3 : (ω, ζ) ∈ BadEscP
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h3)
    by_cases h4 : ∃ s : Fin T, (ω, ζ) ∈ BadMean s
    · rcases h4 with ⟨s, hs⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hs⟩)
    exfalso
    have hop : ∀ x y : Fin n → ℝ, (∑ i, (x i) ^ 2 ≤ 1) → (∑ i, (y i) ^ 2 ≤ 1) →
        |∑ i : Fin n, ∑ j : Fin n, x i * adjSign ω i j * y j| ≤ 20 * Real.sqrt (n : ℝ) := by
      intro x y hx hy; by_contra hgt
      exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, y, hx, hy, lt_of_not_ge hgt⟩⟩)
    have hanti : ∀ s : Finset (Fin n),
        ((Finset.univ.filter (fun v : Fin n =>
          |(Green91.friendliness ((graphEquiv n).symm ω) s v : ℝ)| ≤
            c_anti * Real.sqrt (n : ℝ))).card : ℝ) < (ε / 4) * (n : ℝ) := by
      intro s; by_contra hge
      exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, not_lt.mp hge⟩⟩)
    have hex_s : ∃ s : Fin T,
        ((Finset.univ.filter (fun v : Fin n =>
          |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ) < δ * (n : ℝ) ∧
        ∑ v : Fin n, (iterState lam γ σ ω ζ (s.val + 1) v -
          iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v) ^ 2 < δ₁ * (n : ℝ) := by
      by_contra hall
      push Not at hall
      refine h3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, fun s => ?_⟩)
      by_cases hI : δ * (n : ℝ) ≤ ((Finset.univ.filter (fun v : Fin n =>
          |iterState lam γ σ ω ζ s.val v| ≤ 1 - γ)).card : ℝ)
      · exact Or.inl hI
      · exact Or.inr (hall s (lt_of_not_ge hI))
    rcases hex_s with ⟨s, hIs, hsteps⟩
    have hmeans : |(∑ v : Fin n, iterState lam γ σ ω ζ s.val v) / (n : ℝ)| ≤ δ := by
      by_contra hgt
      exact h4 ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hgt⟩⟩
    have hxt_close : ∀ v : Fin n,
        |iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v - iterState lam γ σ ω ζ s.val v| ≤ γ / 4 := by
      intro v
      have hsub : iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val) v - iterState lam γ σ ω ζ s.val v =
          σ * chi γ (iterState lam γ σ ω ζ s.val v) * kickVal ζ s.val v := by simp [iterKick]
      rw [hsub, abs_mul, abs_mul, abs_of_pos hσ0, abs_of_nonneg (chi_bounds γ _).1]
      calc σ * chi γ (iterState lam γ σ ω ζ s.val v) * |kickVal ζ s.val v|
          ≤ σ * 1 * 2 := mul_le_mul (mul_le_mul_of_nonneg_left (chi_bounds γ _).2 hσ0.le)
            (abs_kickVal_lt_two ζ s.val v).le (abs_nonneg _) (by positivity)
        _ ≤ γ / 4 := by linarith only [hσ]
    exact hfail (round_to_friendly_bisection hn16 hε0 hε1 hγ0 hγ_le16 hδ0 hδ₁0 hc0 hlam0
      hγ_small hδγ_eps hδ₁_small hn_γ hn_ε hn_c ω hop hanti
      (iterState lam γ σ ω ζ s.val)
      (iterKick γ σ ζ s.val (iterState lam γ σ ω ζ s.val))
      (iterState lam γ σ ω ζ (s.val + 1))
      (abs_iterState_lt_one hlam0 ω ζ s.val)
      (fun v => abs_iterKick_lt_one hγ0 hγ_le2 hσ0.le hσ ζ s.val _ v (abs_iterState_lt_one hlam0 ω ζ s.val v))
      hxt_close (fun _ => rfl) hIs hsteps hmeans)
  set NE : ℝ := (Fintype.card (EdgeIdx n → Bool) : ℝ)
  set NK : ℝ := (Fintype.card (KickBits T n) : ℝ)
  have hNK_pos : 0 < NK := Nat.cast_pos.mpr Fintype.card_pos
  have hb1 : (((BadOp ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) ≤
      (p_fail / 10) * (NE * NK) := by
    have h1 : (((BadOp ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) = (BadOp.card : ℝ) * NK := by
      rw [Finset.card_product, Finset.card_univ, Nat.cast_mul]
    rw [h1]
    have hop_b := op_norm_bad_bound hn1
    have h2 : 2 * Real.exp (-2 * (n : ℝ)) ≤ p_fail / 10 := by
      have h3 : 2 / (n : ℝ) ≤ p_fail / 10 := by
        rw [div_le_div_iff₀ hn_pos (by norm_num)]
        have hp_mul := (div_le_iff₀ hp0).mp hn_p
        linarith only [hp_mul, mul_comm p_fail (n : ℝ)]
      have h4 : 2 * (1 / (n : ℝ)) = 2 / (n : ℝ) := by ring
      linarith only [hexp_le, h3, h4]
    calc (BadOp.card : ℝ) * NK ≤ (2 * Real.exp (-2 * (n : ℝ)) * NE) * NK :=
          mul_le_mul_of_nonneg_right hop_b hNK_pos.le
      _ ≤ ((p_fail / 10) * NE) * NK :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)) hNK_pos.le
      _ = (p_fail / 10) * (NE * NK) := by ring
  have hb2 : (((BadAnti ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) ≤
      (p_fail / 10) * (NE * NK) := by
    have h1 : (((BadAnti ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) = (BadAnti.card : ℝ) * NK := by
      rw [Finset.card_product, Finset.card_univ, Nat.cast_mul]
    rw [h1]
    have hanti_b := all_bisections_anticonc (by positivity : 0 < ε / 4) (by linarith only [hε1] : ε / 4 ≤ 1 / 4)
      hc0 hn_anti hn16
    have h2 : (1 / 2 : ℝ) ^ n ≤ p_fail / 10 := by
      have h3 : 1 / (n : ℝ) ≤ p_fail / 10 := by
        rw [div_le_div_iff₀ hn_pos (by norm_num)]
        have hp_mul := (div_le_iff₀ hp0).mp hn_p
        linarith only [hp_mul, mul_comm p_fail (n : ℝ)]
      exact hhalf_le.trans h3
    calc (BadAnti.card : ℝ) * NK ≤ ((1 / 2 : ℝ) ^ n * NE) * NK :=
          mul_le_mul_of_nonneg_right hanti_b hNK_pos.le
      _ ≤ ((p_fail / 10) * NE) * NK :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)) hNK_pos.le
      _ = (p_fail / 10) * (NE * NK) := by ring
  have hb3 : (BadEscP.card : ℝ) ≤ (p_fail / 2) * (NE * NK) :=
    bad_esc_card_le hn1 hT1 hlam0 hlam1 hγ0 hγ_le2 hσ0 hσ hδ0 hδ₁0 hp0 hn_δ hlam_grad hlam_drift hT_ge
  have hb4 : ((Finset.univ.biUnion BadMean).card : ℝ) ≤ (p_fail / 10) * (NE * NK) :=
    bad_mean_card_le hn1 hlam0 hγ0 hγ_le2 hσ0.le hσ hδ0 hp0 hn_var
  have hfail_prod : (FailG.card : ℝ) * NK ≤ p_fail * (NE * NK) := by
    have h1 : (FailG.card : ℝ) * NK = ((FailG ×ˢ (Finset.univ : Finset (KickBits T n))).card : ℝ) := by
      rw [Finset.card_product, Finset.card_univ, Nat.cast_mul]
    have hu : ((FailG ×ˢ (Finset.univ : Finset (KickBits T n))).card : ℝ) ≤
        (((BadOp ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) +
        (((BadAnti ×ˢ (Finset.univ : Finset (KickBits T n))).card) : ℝ) +
        (BadEscP.card : ℝ) + ((Finset.univ.biUnion BadMean).card : ℝ) := by
      have hnat : (FailG ×ˢ (Finset.univ : Finset (KickBits T n))).card ≤
          (BadOp ×ˢ (Finset.univ : Finset (KickBits T n))).card +
          (BadAnti ×ˢ (Finset.univ : Finset (KickBits T n))).card +
          BadEscP.card + (Finset.univ.biUnion BadMean).card := by
        calc _ ≤ ((BadOp ×ˢ Finset.univ) ∪ (BadAnti ×ˢ Finset.univ) ∪ BadEscP ∪
                Finset.univ.biUnion BadMean).card := Finset.card_le_card hcov
          _ ≤ ((BadOp ×ˢ Finset.univ) ∪ (BadAnti ×ˢ Finset.univ) ∪ BadEscP).card +
                (Finset.univ.biUnion BadMean).card := Finset.card_union_le _ _
          _ ≤ ((BadOp ×ˢ Finset.univ) ∪ (BadAnti ×ˢ Finset.univ)).card + BadEscP.card +
                (Finset.univ.biUnion BadMean).card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      exact_mod_cast hnat
    have hnn : (0 : ℝ) ≤ p_fail * (NE * NK) := by positivity
    linarith only [h1, hu, hb1, hb2, hb3, hb4, hnn]
  have hfail_E : (FailG.card : ℝ) ≤ p_fail * NE := by
    rw [← mul_assoc] at hfail_prod
    exact le_of_mul_le_mul_right hfail_prod hNK_pos
  refine prob_ge_of_fail_card_le (P := P) hp0.le ?_
  convert hfail_E using 2
  congr 1; ext ω; simp [FailG]

/-- Fixed-tolerance theorem: for any `ε ∈ (0, 1)`, w.h.p. `G(n, 1/2)` has a bisection
with at least `(1 - ε) n` strictly friendly vertices. -/
theorem fixed_eps_tendsto {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => Green91.prob n fun G =>
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (1 - ε) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ)) atTop (𝓝 1) := by
  rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
  intro e he
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt he.ne'
  let p_fail : ℝ := 1 / ((m + 2 : ℕ) : ℝ)
  have hp0 : 0 < p_fail := by positivity
  have hofReal_p : ENNReal.ofReal p_fail ≤ e := by
    have h1 : ENNReal.ofReal p_fail = ((m + 2 : ℕ) : ENNReal)⁻¹ := by
      simp only [p_fail, one_div]
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
    rw [h1]
    have h2 : ((m + 2 : ℕ) : ENNReal)⁻¹ ≤ ((m : ℕ) : ENNReal)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast (by omega : m ≤ m + 2))
    exact h2.trans hm.le
  -- Acyclic parameter schedule depending ONLY on `(ε, p_fail)`.
  let M_anti : ℕ := Nat.ceil (1 / (ε / 4))
  let c_anti : ℝ := (1 / 12) * (1 / 8 : ℝ) ^ M_anti
  have hc0 : 0 < c_anti := by positivity
  let γ : ℝ := min (ε / 64) (ε * c_anti ^ 2 / 400000)
  have hγ0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hγ_le16 : γ ≤ 1 / 16 := (min_le_left _ _).trans (by linarith only [hε1])
  let δ : ℝ := γ
  let σ : ℝ := γ / 8
  have hσ0 : 0 < σ := by positivity
  let θ_step : ℝ := min (1 / 4) (c_anti / 40)
  have hθ_pos : 0 < θ_step := lt_min (by norm_num) (by positivity)
  let δ₁ : ℝ := (ε / 8) * θ_step ^ 2
  have hδ₁0 : 0 < δ₁ := by positivity
  let d₀ : ℝ := min (γ / 8) ((1 / 40) * σ * Real.sqrt (δ / 200))
  have hd₀_pos : 0 < d₀ := lt_min (by positivity) (by positivity)
  let c_esc : ℝ := 5 * δ * (δ ^ 2 / 600000) * d₀ ^ 2
  have hcesc_pos : 0 < c_esc := by positivity
  have hmin_pos : 0 < min c_esc (5 * δ₁) := lt_min hcesc_pos (by positivity)
  let T : ℕ := Nat.ceil (122 / (p_fail * min c_esc (5 * δ₁))) + 1
  have hT1 : 1 ≤ T := Nat.le_add_left 1 _
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  have hT_ge : 122 / (p_fail * min c_esc (5 * δ₁)) ≤ (T : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  let lam : ℝ := min (1 / 4) (min ((γ / 16) * ((1 / 40) * σ * Real.sqrt (δ / 200)))
    (γ / (320 * (T : ℝ) * σ)))
  have hlam0 : 0 < lam := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hlam1 : lam ≤ 1 / 4 := min_le_left _ _
  have hlam_grad : 16 * lam / γ ≤ (1 / 40) * σ * Real.sqrt (δ / 200) := by
    have h1 : lam ≤ (γ / 16) * ((1 / 40) * σ * Real.sqrt (δ / 200)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [div_le_iff₀ hγ0]
    linarith only [h1]
  have hlam_drift : (T : ℝ) * (320 * lam * σ / γ) ≤ 1 := by
    have h1 : lam ≤ γ / (320 * (T : ℝ) * σ) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (T : ℝ) * (320 * lam * σ / γ) = lam * (320 * (T : ℝ) * σ) / γ := by ring
    rw [h2, div_le_one hγ0]
    exact (le_div_iff₀ (by positivity)).mp h1
  have hγ_small : 400 * (12 * δ + 13 * γ) ≤ (ε / 8) * (c_anti / 2) ^ 2 := by
    have hle : γ ≤ ε * c_anti ^ 2 / 400000 := min_le_right _ _
    have h1 : (ε / 8) * (c_anti / 2) ^ 2 = ε * c_anti ^ 2 / 32 := by ring
    have h2 : 0 ≤ ε * c_anti ^ 2 := by positivity
    simp only [δ]; linarith only [hle, h1, h2]
  have hδγ_eps : 3 * δ + 2 * γ ≤ ε / 8 := by
    have hle : γ ≤ ε / 64 := min_le_left _ _
    simp only [δ]; linarith only [hle, hε0]
  let C_rem_max : ℝ := (T : ℝ) * (6 : ℝ) ^ T * (64 : ℝ) ^ T * (1 + 100 / γ + 1 / Real.sqrt lam)
  let C_var_max : ℝ := ((T : ℝ) ^ 2 + 8 * (T : ℝ)) * (36 : ℝ) ^ T + 2 * ((T : ℝ) + 1) * C_rem_max ^ 2
  let R_big : ℝ := max (4 / γ) (max (16 / ε) (max (4 / c_anti ^ 2) (max (16 / (3 * c_anti) ^ 2)
    (max (20 / p_fail) (10 * (T : ℝ) * (C_var_max + 8 * ((T : ℝ) + 1)) / (δ ^ 2 * p_fail))))))
  let N₀ : ℕ := max 16 (Nat.ceil R_big + 1)
  filter_upwards [eventually_ge_atTop N₀] with n hn_ge
  have hn16 : 16 ≤ n := le_trans (le_max_left _ _) hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hn_R : R_big ≤ (n : ℝ) := by
    have h1 : Nat.ceil R_big ≤ n := le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hn_ge)
    exact (Nat.le_ceil R_big).trans (by exact_mod_cast h1)
  have hn_γ : 4 ≤ γ * (n : ℝ) := by
    have h1 : 4 / γ ≤ (n : ℝ) := (le_max_left _ _).trans hn_R
    rw [mul_comm]; exact (div_le_iff₀ hγ0).mp h1
  have hn_ε : 16 ≤ ε * (n : ℝ) := by
    have h1 : 16 / ε ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hn_R)
    rw [mul_comm]; exact (div_le_iff₀ hε0).mp h1
  have hn_c : 2 ≤ c_anti * Real.sqrt (n : ℝ) := by
    have h1 : 4 / c_anti ^ 2 ≤ (n : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn_R))
    exact sqrt_ge_of_sq_div_le (by norm_num) hc0 hn_pos (by norm_num; exact h1)
  have hn_anti : 6 * c_anti + 4 / Real.sqrt (n : ℝ) ≤ (1 / 8 : ℝ) ^ M_anti := by
    have h1 : 16 / (3 * c_anti) ^ 2 ≤ (n : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans hn_R)))
    have h3 : 4 ≤ (3 * c_anti) * Real.sqrt (n : ℝ) :=
      sqrt_ge_of_sq_div_le (by norm_num) (by positivity) hn_pos (by norm_num; exact h1)
    have h4 : 4 / Real.sqrt (n : ℝ) ≤ 3 * c_anti := (div_le_iff₀ hsq_pos).mpr h3
    have h9 : 9 * c_anti ≤ (1 / 8 : ℝ) ^ M_anti := by
      simp only [c_anti]; linarith only [show (0 : ℝ) < (1 / 8 : ℝ) ^ M_anti by positivity]
    linarith only [h4, h9]
  have hn_p : 20 / p_fail ≤ (n : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn_R))))
  have hn_var : 10 * (T : ℝ) * (C_var_max + 8 * ((T : ℝ) + 1)) / (δ ^ 2 * p_fail) ≤ (n : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn_R))))
  have hge := fixed_eps_single_n hn16 hT1 hε0 hε1 hp0 hc0 hγ0 hγ_le16 hγ0 hσ0 le_rfl hδ₁0 hlam0 hlam1
    hγ_small hδγ_eps le_rfl hlam_grad hlam_drift hT_ge hn_γ (by linarith only [hn_γ]) hn_ε hn_c
    hn_anti hn_p hn_var
  have hle1 : Green91.prob n (fun G =>
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (1 - ε) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ)) ≤ 1 := by
    change SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩ _ ≤ 1
    exact MeasureTheory.prob_le_one
  exact ⟨(tsub_le_tsub_left hofReal_p 1).trans hge, hle1.trans (le_add_right le_rfl)⟩

end RoundingAndMain

end Green91FKNSS

theorem OMA.solution : type_of% @Green91.green_91.variants.fknss := by
  have hfixed : ∀ k : ℕ, Filter.Tendsto (fun n : ℕ => Green91.prob n fun G =>
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (1 - 1 / ((k + 2 : ℕ) : ℝ)) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ))
      Filter.atTop (nhds 1) := fun k => by
    refine Green91FKNSS.fixed_eps_tendsto (by positivity) ?_
    rw [div_lt_one (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))]
    exact_mod_cast (by omega : 1 < k + 2)
  obtain ⟨k, hk_top, hk_tendsto⟩ := Green91FKNSS.diag_extract
    (fun k n => Green91.prob n fun G =>
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (1 - 1 / ((k + 2 : ℕ) : ℝ)) * (n : ℝ) ≤ (Green91.numFriendly G s : ℝ)) hfixed
  refine ⟨fun n : ℕ => (n : ℝ) / ((k n + 2 : ℕ) : ℝ), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / c)
    filter_upwards [hk_top.eventually (Filter.eventually_ge_atTop K)] with n hn
    simp only [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k n + 2 : ℕ) : ℝ))]
    have hKc : 1 ≤ c * ((k n + 2 : ℕ) : ℝ) := by
      have h1 : 1 / c < ((k n + 2 : ℕ) : ℝ) :=
        hK.trans_le (by exact_mod_cast (by omega : K ≤ k n + 2))
      rw [mul_comm]; exact ((div_lt_iff₀ hc).mp h1).le
    calc (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
      _ ≤ (c * ((k n + 2 : ℕ) : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right hKc (Nat.cast_nonneg n)
      _ = c * (n : ℝ) * ((k n + 2 : ℕ) : ℝ) := by ring
  · refine hk_tendsto.congr fun n => ?_
    congr 1
    ext G
    refine exists_congr fun s => and_congr_right fun _ => ?_
    have heq : (1 - 1 / ((k n + 2 : ℕ) : ℝ)) * (n : ℝ) = (n : ℝ) - (n : ℝ) / ((k n + 2 : ℕ) : ℝ) := by
      ring
    rw [heq]

