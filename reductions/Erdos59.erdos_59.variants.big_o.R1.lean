import FormalConjectures.ErdosProblems.«59»

-- Reduction Erdos59.erdos_59.variants.big_o.R1 of the weak form of Erdős Problem 59
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Counting `H`-free graphs from the growth rate of the extremal number

The target says: if `H` contains a cycle, then the number of `H`-free graphs on `n` vertices is
at most `2 ^ (C * ex(n; H))` for large `n`.

Following A. Ferber, G. McKinley and W. Samotij, *Supersaturated sparse graphs and hypergraphs*,
Int. Math. Res. Not. IMRN 2020, arXiv:1710.04517:
* `H1` (Ferber–McKinley–Samotij, Theorem 2): if `H` contains a cycle and
  `ex(n; H) ≤ A * n ^ α` for all `n`, then there are at most `2 ^ (C * n ^ α)` `H`-free graphs
  on `n` vertices, for all `n`. This is a published theorem. It is the deep input.
* `H2` (open): the target for the bipartite `H` whose extremal number has no polynomial order,
  that is, there is no `α > 0` with `ex(n; H)` of order `n ^ α`. This is a special case of the
  target.

`H2` holds vacuously if `ex(n; H)` has order `n ^ α` for every bipartite `H` containing a cycle.
That is Conjecture 4 of the same paper, a weak form of the Erdős–Simonovits conjecture
(Erdős Problem 713), which asks for `ex(n; H) ∼ c * n ^ α`. So the target follows from `H1` and
that conjecture, as the paper states after its Theorem 2. The order of `ex(n; H)` is known for
`C₄`, `C₆`, `C₁₀` and `K_{s,t}` with `t > (s - 1)!`, so `H2` excludes these graphs.

`main` proves the non-bipartite case directly. The bipartite Turán graph on `n` vertices is
`H`-free and has at least `(n ^ 2 - 1) / 4` edges, and there are at most `2 ^ (n choose 2)` graphs
on `n` vertices. For bipartite `H` with `ex(n; H)` of order `n ^ α`, `main` extends the upper
bound to all `n`, applies `H1`, and uses the lower bound to replace `n ^ α` by `ex(n; H)`.
-/

namespace OMA.R_Erdos59_erdos_59_variants_big_o_R1

open Filter SimpleGraph

/-- Ferber–McKinley–Samotij, Theorem 2: a polynomial upper bound on `ex(n; H)` gives the same
bound on the logarithm of the number of `H`-free graphs. -/
def H1 : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), ¬ H.IsAcyclic → ∀ α A : ℝ, 0 < α → 0 < A →
    (∀ n : ℕ, (extremalNumber n H : ℝ) ≤ A * (n : ℝ) ^ α) →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (Erdos59.numFree H n : ℝ) ≤ (2 : ℝ) ^ (C * (n : ℝ) ^ α)

/-- The target for bipartite `H` such that `ex(n; H)` has order `n ^ α` for no `α > 0`. -/
def H2 : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite → ¬ H.IsAcyclic →
    (¬ ∃ α a A : ℝ, 0 < α ∧ 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      a * (n : ℝ) ^ α ≤ (extremalNumber n H : ℝ) ∧ (extremalNumber n H : ℝ) ≤ A * (n : ℝ) ^ α) →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (Erdos59.numFree H n : ℝ) ≤ (2 : ℝ) ^ (C * (extremalNumber n H : ℝ))

/-- There are at most `2 ^ (n choose 2)` graphs on `n` vertices. -/
lemma numFree_le {k : ℕ} (H : SimpleGraph (Fin k)) (n : ℕ) :
    Erdos59.numFree H n ≤ 2 ^ n.choose 2 := by
  classical
  let S : Set (SimpleGraph (Fin n)) := {G | H.Free G}
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card']
  calc
    S.toFinset.card ≤ ((⊤ : SimpleGraph (Fin n)).edgeFinset.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun G : SimpleGraph (Fin n) => G.edgeFinset)
      · intro G _
        exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (edgeFinset_mono le_top))
      · intro G _ G' _ h
        exact edgeFinset_inj.mp h
    _ = 2 ^ n.choose 2 := by
      rw [Finset.card_powerset, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- The trivial upper bound `ex(n; H) ≤ n choose 2`. -/
lemma extremalNumber_le_choose {k : ℕ} (H : SimpleGraph (Fin k)) (n : ℕ) :
    extremalNumber n H ≤ n.choose 2 := by
  classical
  suffices h : extremalNumber (Fintype.card (Fin n)) H ≤ n.choose 2 by
    simpa only [Fintype.card_fin] using h
  apply (extremalNumber_le_iff (V := Fin n) H _).mpr
  intro G _ _
  simpa only [Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two

lemma choose_two_le_sq (n : ℕ) : n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right, sq]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))

/-- The bipartite Turán graph is `H`-free for non-bipartite `H`. -/
lemma free_turanGraph_two {k : ℕ} (H : SimpleGraph (Fin k)) (hH : ¬ H.IsBipartite) (n : ℕ) :
    H.Free (turanGraph n 2) := by
  rintro ⟨f⟩
  apply hH
  have col : (turanGraph n 2).Colorable 2 :=
    ⟨Coloring.mk (fun v => (⟨v.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))
      (fun {v w} h heq => (turanGraph_adj.mp h) (congrArg Fin.val heq))⟩
  exact col.of_hom f.toHom

/-- A non-bipartite `H` has `ex(n; H) ≥ (n ^ 2 - 1) / 4`. -/
lemma sq_le_extremalNumber {k : ℕ} (H : SimpleGraph (Fin k)) (hH : ¬ H.IsBipartite) (n : ℕ) :
    n ^ 2 ≤ 4 * extremalNumber n H + 1 := by
  have h := card_edgeFinset_le_extremalNumber (free_turanGraph_two H hH n)
  rw [Fintype.card_fin, card_edgeFinset_turanGraph] at h
  have h2 : (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) ≤ extremalNumber n H :=
    (Nat.le_add_right _ _).trans h
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    have e : ((2 * m) ^ 2 - (2 * m % 2) ^ 2) * (2 - 1) / (2 * 2) = m ^ 2 := by
      rw [Nat.mul_mod_right]
      have : (2 * m) ^ 2 - 0 ^ 2 = m ^ 2 * 4 := by ring_nf; omega
      rw [this]
      omega
    rw [e] at h2
    nlinarith
  · subst hm
    have e : ((2 * m + 1) ^ 2 - ((2 * m + 1) % 2) ^ 2) * (2 - 1) / (2 * 2) = m ^ 2 + m := by
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      rw [h1]
      have : (2 * m + 1) ^ 2 - 1 ^ 2 = (m ^ 2 + m) * 4 := by
        have : (2 * m + 1) ^ 2 = (m ^ 2 + m) * 4 + 1 := by ring
        omega
      rw [this]
      omega
    rw [e] at h2
    nlinarith

theorem main : H1 → H2 → type_of% @Erdos59.erdos_59.variants.big_o := by
  intro h1 h2 k H hcyc
  by_cases hbip : H.IsBipartite
  · by_cases hreg : ∃ α a A : ℝ, 0 < α ∧ 0 < a ∧ ∀ᶠ n : ℕ in atTop,
        a * (n : ℝ) ^ α ≤ (extremalNumber n H : ℝ) ∧
          (extremalNumber n H : ℝ) ≤ A * (n : ℝ) ^ α
    swap
    · exact h2 k H hbip hcyc hreg
    obtain ⟨α, a, A, hα, ha, hev⟩ := hreg
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hA' : 0 < max A ((N : ℝ) ^ 2) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
      linarith [le_max_right A ((N : ℝ) ^ 2)]
    have hall : ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ (max A ((N : ℝ) ^ 2) + 1) * (n : ℝ) ^ α := by
      intro n
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n) α
      rcases le_or_gt N n with hn | hn
      · refine (hN n hn).2.trans (mul_le_mul_of_nonneg_right ?_ hpow)
        linarith [le_max_left A ((N : ℝ) ^ 2)]
      · have hex : (extremalNumber n H : ℝ) ≤ (n : ℝ) ^ 2 := by
          exact_mod_cast (extremalNumber_le_choose H n).trans (choose_two_le_sq n)
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · have h0 : (extremalNumber 0 H : ℝ) ≤ 0 := by simpa using hex
          rw [Nat.cast_zero, Real.zero_rpow hα.ne', mul_zero]
          exact h0
        · have hone : (1 : ℝ) ≤ (n : ℝ) ^ α :=
            Real.one_le_rpow (by exact_mod_cast hpos) hα.le
          have hnN : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
            have : (n : ℝ) ≤ N := by exact_mod_cast hn.le
            exact pow_le_pow_left₀ (Nat.cast_nonneg n) this 2
          calc
            (extremalNumber n H : ℝ) ≤ (max A ((N : ℝ) ^ 2) + 1) * 1 := by
              linarith [le_max_right A ((N : ℝ) ^ 2)]
            _ ≤ _ := mul_le_mul_of_nonneg_left hone hA'.le
    obtain ⟨C, hC, hcount⟩ := h1 k H hcyc α _ hα hA' hall
    refine ⟨C / a, div_pos hC ha, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (hcount n).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith [(hN n hn).1]
  · refine ⟨5, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hsq := sq_le_extremalNumber H hbip n
    have hex : n ^ 2 ≤ 5 * extremalNumber n H := by nlinarith
    have hexp : ((n.choose 2 : ℕ) : ℝ) ≤ 5 * (extremalNumber n H : ℝ) := by
      exact_mod_cast (choose_two_le_sq n).trans hex
    calc
      (Erdos59.numFree H n : ℝ) ≤ (2 : ℝ) ^ (n.choose 2 : ℕ) := by
        exact_mod_cast numFree_le H n
      _ = (2 : ℝ) ^ ((n.choose 2 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end OMA.R_Erdos59_erdos_59_variants_big_o_R1
