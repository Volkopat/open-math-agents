import FormalConjectures.Wikipedia.HardyLittlewood

/-! Separate convergence of the singular series from the estimate for counts using finite
products of local factors. A tuple covering an odd prime modulus satisfies the target
identically, since the upstream counting function includes the admissibility condition.
The product estimates adapt @senamakel's proof of Richards' incompatibility theorem. -/

namespace OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R1

open HardyLittlewood Filter Asymptotics
open scoped Topology

/-- The product over the odd primes converges to a strictly positive value. -/
def H1 : Prop :=
  ∀ {k : ℕ} (m : Fin k.succ → ℕ), Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    ∃ L : ℝ, 0 < L ∧ HasProd (fun q : {q : ℕ // q.Prime ∧ 3 ≤ q} =>
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ k.succ) L

/-- For a sufficiently large finite set of odd primes, its local factors approximate the
integral-normalized count to any fixed accuracy once the counting cutoff is large enough. -/
def H2 : Prop :=
  ∀ {k : ℕ} (m : Fin k.succ → ℕ), m 0 = 0 → (∀ i ≠ 0, Even (m i)) →
    Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} in atTop,
    ∀ᶠ n : ℕ in atTop, dist ((Nat.primeTupleCounting m n : ℝ) /
      (∫ t in (2 : ℝ)..n, 1 / t.log ^ k.succ))
      (2 ^ k * ∏ q ∈ s,
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ k.succ) < ε

/-- The elementary estimate behind the convergence of the singular series:
`|(1 - n x)/(1 - x)^n - 1| ≤ 2 n² x²` when `0 < x` and `n x ≤ 1/2`. -/
lemma factor_sub_one_le (n : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1' : x ≤ 1)
    (hx1 : (n : ℝ) * x ≤ 1 / 2) :
    |(1 - n * x) / (1 - x) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * x ^ 2 := by
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx0.le
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 - x) ^ n := ⟨_, rfl⟩
  rw [← hP]
  have hlow : 1 - n * x ≤ P := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) n
    rw [← sub_eq_add_neg, ← hP] at h
    linarith
  have hup : P ≤ 1 - n * x + (n * x) ^ 2 := by
    have h1 : P ≤ Real.exp (-x) ^ n := by
      rw [hP]
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) n
    have h2 : Real.exp (-x) ^ n = Real.exp (-(n * x)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 := Real.abs_exp_sub_one_sub_id_le (x := -(n * x))
      (by rw [abs_neg, abs_of_nonneg hnx]; linarith)
    have h4 := (abs_le.mp h3).2
    rw [neg_sq] at h4
    linarith
  have hP0 : 0 < P := by linarith
  rw [div_sub_one hP0.ne', abs_div, abs_of_pos hP0, div_le_iff₀ hP0,
    abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg x))
    (by linarith : (0 : ℝ) ≤ 2 * P - 1)]

/-- The same estimate at `x = 1/q`. -/
lemma factor_sub_one_le' (n : ℕ) (q : ℝ) (hq : 2 * (n : ℝ) ≤ q) (hq1 : 1 ≤ q) :
    |(1 - (n : ℝ) / q) / (1 - 1 / q) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have h := factor_sub_one_le n (1 / q) (by positivity) (by rw [div_le_one hq0]; exact hq1)
    (by rw [mul_one_div, div_le_iff₀ hq0]; linarith)
  rwa [mul_one_div, one_div_pow] at h

/-- A product of Hardy–Littlewood factors is positive when the tuple misses a class mod every
prime and occupies `k + 1` distinct classes mod every large prime. -/
lemma positive_product {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (hlt : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ) :
    ∃ L : ℝ, 0 < L ∧ HasProd (fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} =>
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ) L := by
  set f : { q : ℕ // q.Prime ∧ 3 ≤ q} → ℝ :=
    fun q => (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ with hf
  have hpos : ∀ q, 0 < f q := by
    intro q
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hl : (Nat.numResidues q t : ℝ) < (q : ℕ) := by exact_mod_cast hlt q
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hg : Summable fun q => f q - 1 := by
    have hs : Summable fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * ((k.succ : ℕ) : ℝ) ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic (B + 2 * k.succ)).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_Iic]
    by_contra hbig
    apply hq
    have hbig' : B + 2 * k.succ < (q : ℕ) := by omega
    have hq' : 2 * ((k.succ : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * k.succ ≤ (q : ℕ))
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (q : ℕ))
    rw [Real.norm_eq_abs, hf]
    dsimp only
    rw [heq _ (by omega)]
    exact factor_sub_one_le' k.succ _ hq' hq1
  have hlog : Summable fun q => Real.log (f q) :=
    (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]
  refine ⟨∏' q, f q, ?_, (Real.multipliable_of_summable_log hpos hlog).hasProd⟩
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

theorem euler_product : H1 := by
  intro k m hinj hlocal
  classical
  let B := Finset.univ.sup m
  apply positive_product m B
  · intro q
    have : NeZero (q : ℕ) := ⟨q.property.1.ne_zero⟩
    unfold HardyLittlewood.Nat.numResidues
    calc
      _ < Nat.card (ZMod (q : ℕ)) := Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
      _ = (q : ℕ) := Nat.card_zmod _
  · intro q hq
    have hsmall (i) : m i < q := (Finset.le_sup (f := m) (Finset.mem_univ i)).trans_lt hq
    have hj : Function.Injective (fun i => (m i : ZMod q)) := by
      intro i j he
      have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp he
      rw [Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)] at h
      exact hinj h
    unfold HardyLittlewood.Nat.numResidues
    rw [Set.ncard_range_of_injective hj]
    simp

lemma obstructed {k : ℕ} (m : Fin k.succ → ℕ) (q : {q : ℕ // q.Prime ∧ 3 ≤ q})
    (hs : Function.Surjective (fun i => (m i : ZMod q))) :
    FirstHardyLittlewoodConjectureFor m := by
  classical
  intro _ _ _
  have hcount (n : ℕ) : Nat.primeTupleCounting m n = 0 := by
    unfold Nat.primeTupleCounting
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply hp.2 q q.property.1
    intro z
    obtain ⟨i, hi⟩ := hs (z - (p : ZMod q))
    exact ⟨i, by dsimp at hi; simpa [hi] using (add_sub_cancel_left (p : ZMod q) z)⟩
  have hnum : Nat.numResidues q m = q := by
    unfold Nat.numResidues
    rw [Set.range_eq_univ.mpr hs, Set.ncard_univ, Nat.card_zmod]
  have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.property.1.ne_zero
  have hprod : (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - (Nat.numResidues p m : ℝ) / p) / (1 - 1 / p) ^ k.succ) = 0 := by
    apply (hasProd_zero_of_exists_eq_zero _).tprod_eq
    exact ⟨q, by simp [hnum, hq]⟩
  simpa only [hcount, Nat.cast_zero, hprod, mul_zero, zero_mul] using
    (IsEquivalent.refl : (fun _ : ℕ => (0 : ℝ)) ~[atTop] (fun _ => 0))

theorem main : H1 → H2 → type_of% @HardyLittlewood.first_hardy_littlewood_conjecture := by
  intro hprod hcount k m
  classical
  by_cases hlocal : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q},
      ¬ Function.Surjective (fun i => (m i : ZMod q))
  · intro hzero heven hinj
    obtain ⟨L, hpos, hL⟩ := hprod m hinj hlocal
    let f := fun q : {q : ℕ // q.Prime ∧ 3 ≤ q} =>
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ k.succ
    let I := fun n : ℕ => ∫ t in (2 : ℝ)..n, 1 / t.log ^ k.succ
    let P := fun n : ℕ => (Nat.primeTupleCounting m n : ℝ)
    have hp : Tendsto (fun s : Finset _ => ∏ q ∈ s, f q) atTop (𝓝 L) := hL
    have hc := hp.const_mul ((2 : ℝ)^k)
    have hlim : Tendsto (fun n => P n / I n) atTop (𝓝 (2^k * L)) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨s, hs, hnear⟩ := ((hcount m hzero heven hinj hlocal (ε/2) (half_pos hε)).and
        (Metric.tendsto_nhds.mp hc (ε/2) (half_pos hε))).exists
      filter_upwards [hs] with n hn
      exact (dist_triangle _ _ _).trans_lt
        ((add_lt_add hn hnear).trans_eq (add_halves ε))
    change P ~[atTop] fun n => (2^k * ∏' q, f q) * I n
    rw [show (∏' q, f q) = L from hL.tprod_eq]
    have hC : (2 : ℝ)^k * L ≠ 0 := by positivity
    apply isEquivalent_of_tendsto_one
    convert hlim.div_const (2^k * L) using 1
    · ext n
      simp [Pi.div_apply, div_div, mul_comm]
    · simp [hC]
  · push Not at hlocal
    obtain ⟨q, hq⟩ := hlocal
    exact obstructed m q hq

end OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R1
