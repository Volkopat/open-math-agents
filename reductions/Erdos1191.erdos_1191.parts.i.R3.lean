import FormalConjectures.ErdosProblems.«1191»

-- Reduction Erdos1191.erdos_1191.parts.i.R3 of Erdős Problem 1191 — i
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A threshold-doubling (density decrement) reduction of Erdős Problem 1191 (i)

Write `c_j(S) = |S ∩ [1, 2^j]|` for a finite Sidon set `S`, and say that the threshold
`a` is *attainable* if for every `J` there is a horizon `K ≥ J` such that every Sidon
`S ⊆ [1, 2^K]` has a scale `j ∈ [J, K]` with `a * c_j ^ 2 * j ≤ 512 * 2 ^ j`.

* `H1` (base, the classical Erdős block bound in finite dyadic form): in every exponent
  window `[R, 2R]` with `R ≥ 16` some scale has `c_k ^ 2 * k ≤ 512 * 2 ^ k`. This makes
  the threshold `1` attainable.
* `H2` (decrement step): attainable thresholds are closed under doubling.

Iterating `H2` makes every threshold `2 ^ n` attainable; together with the finite-to-infinite
transfer below this gives liminf zero. Both hypotheses are consequences of the target.
-/

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R3

open Filter
open Set

theorem liminf_ofReal_zero_of_frequently {u : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ x in atTop, u x ≤ ε) :
    liminf (fun x ↦ ENNReal.ofReal (u x)) atTop = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  apply Filter.liminf_le_of_frequently_le'
  refine (h ε (by exact_mod_cast hε)).mono fun x hx => ?_
  exact ENNReal.ofReal_le_of_le_toReal (by simpa using hx)

theorem normalised_le_of_sq_le {n x : ℕ} {ε : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    (h : (n : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x) :
    (n : ℝ) / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) ≤ ε := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_mul_eq_mul_div,
    div_le_iff₀ (Real.sqrt_pos.2 hx0)]
  have h1 : (n : ℝ) * Real.sqrt (Real.log x) = Real.sqrt ((n : ℝ) ^ 2 * Real.log x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
  have h2 : ε * Real.sqrt x = Real.sqrt (ε ^ 2 * x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
  rw [h1, h2]
  exact Real.sqrt_le_sqrt h

theorem prefix_filter_card (S : Finset ℕ) (hS : ∀ a ∈ S, 1 ≤ a) (x : ℕ) :
    (S.filter (· ≤ x)).card = ((S : Set ℕ) ∩ Icc 1 x).ncard := by
  have h : (↑(S.filter (· ≤ x)) : Set ℕ) = (S : Set ℕ) ∩ Icc 1 x := by
    ext a
    simp only [Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_Icc]
    exact ⟨fun ha => ⟨ha.1, hS a ha.1, ha.2⟩, fun ha => ⟨ha.1, ha.2.2⟩⟩
  rw [← h, ncard_coe_finset]

/-- The finite dyadic obstruction suffices for the squared critical density bound. -/
theorem core_sq_from_finite_obstruction
    (h : ∀ d J : ℕ, 0 < d → ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j)
    (A : Set ℕ) (hS : IsSidon A) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨d, hd⟩ := exists_nat_ge (Real.log 2 / ε ^ 2)
  have hdpos : 0 < d := by
    exact_mod_cast (div_pos hlog hεsq).trans_le hd
  have hdlog : Real.log 2 ≤ (d : ℝ) * ε ^ 2 := (div_le_iff₀ hεsq).mp hd
  obtain ⟨K, _, hK⟩ := h d N hdpos
  have hfin : (A ∩ Icc 1 (2 ^ K)).Finite :=
    (finite_Icc _ _).subset inter_subset_right
  let S := hfin.toFinset
  have hcoe : (S : Set ℕ) = A ∩ Icc 1 (2 ^ K) := hfin.coe_toFinset
  have hsub : (S : Set ℕ) ⊆ Icc 1 (2 ^ K) := hcoe ▸ inter_subset_right
  have hsid : IsSidon (S : Set ℕ) := by
    rw [hcoe]
    intro a ha b hb c hc e he heq
    exact hS a ha.1 b hb.1 c hc.1 e he.1 heq
  obtain ⟨j, hj, hjcount⟩ := hK S hsub hsid
  obtain ⟨hNj, hjK⟩ := Finset.mem_Icc.mp hj
  have hpow : (2 : ℕ) ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hjK
  rw [prefix_filter_card S (fun a ha => (hsub ha).1), hcoe, inter_assoc,
    inter_eq_right.mpr (Icc_subset_Icc_right hpow)] at hjcount
  let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
  have hcount : (d : ℝ) * m ^ 2 * (j : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast hjcount
  refine ⟨2 ^ j, hNj.trans Nat.lt_two_pow_self.le, Nat.succ_le_of_lt (by positivity), ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  change m ^ 2 * ((j : ℝ) * Real.log 2) ≤ ε ^ 2 * (2 : ℝ) ^ j
  calc
    _ ≤ m ^ 2 * ((j : ℝ) * ((d : ℝ) * ε ^ 2)) := by gcongr
    _ = ε ^ 2 * ((d : ℝ) * m ^ 2 * (j : ℝ)) := by ring
    _ ≤ ε ^ 2 * (2 : ℝ) ^ j := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hεsq.le

/-- Base: the Erdős block bound in finite dyadic form. -/
def H1 : Prop :=
  ∀ (R : ℕ) (S : Finset ℕ), 16 ≤ R → (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R)) →
    IsSidon (↑S : Set ℕ) →
      ∃ k ∈ Set.Icc R (2 * R), (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 512 * 2 ^ k

/-- Decrement step: if the dyadic threshold `a` is attainable at arbitrarily late scales
uniformly over finite Sidon sets, then so is `2 * a`. -/
def H2 : Prop :=
  ∀ a : ℕ,
    (∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, a * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 512 * 2 ^ j) →
    (∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, (2 * a) * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 512 * 2 ^ j)

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.i := by
  intro hH1 hH2 A _hinf hS
  have hpow : ∀ n : ℕ, ∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, 2 ^ n * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 512 * 2 ^ j := by
    intro n
    induction n with
    | zero =>
      intro J
      refine ⟨2 * max 16 J, by omega, fun S hsub hsid => ?_⟩
      obtain ⟨k, hk, hkc⟩ := hH1 (max 16 J) S (le_max_left _ _) hsub hsid
      refine ⟨k, Finset.mem_Icc.mpr ⟨(le_max_right 16 J).trans hk.1, hk.2⟩, ?_⟩
      simpa using hkc
    | succ n ih =>
      have := hH2 (2 ^ n) ih
      simpa only [pow_succ, mul_comm 2 (2 ^ n)] using this
  have hobs : ∀ d J : ℕ, 0 < d → ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j := by
    intro d J _hd
    obtain ⟨K, hKJ, hK⟩ := hpow (9 + d) J
    refine ⟨K, hKJ, fun S hsub hsid => ?_⟩
    obtain ⟨j, hj, hjc⟩ := hK S hsub hsid
    refine ⟨j, hj, ?_⟩
    have hd2 : 512 * d ≤ 2 ^ (9 + d) := by
      rw [pow_add]
      exact Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    have h1 : 512 * (d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) ≤
        2 ^ (9 + d) * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j := by
      calc 512 * (d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j)
          = (512 * d) * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j := by ring
        _ ≤ _ := by gcongr
    omega
  apply liminf_ofReal_zero_of_frequently
  intro ε hε
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨x, hNx, hx1, hx⟩ := core_sq_from_finite_obstruction hobs A hS ε hε N
  exact ⟨x, hNx, normalised_le_of_sq_le hε hx1 hx⟩

end OMA.R_Erdos1191_erdos_1191_parts_i_R3
