import OMAStatements.S_oeis_a081601

-- Source: https://oeis.org/A081601
-- Lucas's theorem groups the central binomial coefficients into triples
-- with residues c, 2c, and 0. The surviving indices are three times the
-- ternary values of binary strings, listed in their natural order.
open Finset

private def central (k : ℕ) : ℕ := (2 * k).choose k

private theorem lucas (q r : ℕ) (hr : r < 3) :
    central (3 * q + r) % 3 = ((r + 1) * central q) % 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 2 * (3 * q + r)) (k := 3 * q + r) (p := 3)
  rw [show 2 * (3 * q + r) % 3 = 2 * r % 3 by omega,
    show (3 * q + r) % 3 = r by omega,
    show 2 * (3 * q + r) / 3 = 2 * q + 2 * r / 3 by omega,
    show (3 * q + r) / 3 = q by omega] at h
  interval_cases r
  · simpa [central, Nat.ModEq] using h
  · simpa [central, Nat.ModEq] using h
  · have h' : central (3 * q + 2) % 3 = 0 := by
      simpa [central, Nat.ModEq, Nat.choose_eq_zero_of_lt] using h
    omega

private def partialSum (m : ℕ) : ℕ := ∑ k ∈ range m, central k
private theorem partial_succ (m : ℕ) :
    partialSum (m + 1) = partialSum m + central m := sum_range_succ central m

private theorem sum_block (q : ℕ) : partialSum (3 * q) % 3 = 0 := by
  induction q with
  | zero => simp [partialSum]
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 1 + 1 + 1 by omega]
    simp only [partial_succ]
    have h₀ := lucas q 0 (by decide)
    simp only [add_zero] at h₀
    have h₁ := lucas q 1 (by decide)
    have h₂ := lucas q 2 (by decide)
    rw [show 3 * q + 1 + 1 = 3 * q + 2 by omega]
    omega

private theorem goodPartial (m : ℕ) :
    (¬ 3 ∣ partialSum (m + 1)) ↔ m % 3 = 0 ∧ ¬ 3 ∣ central (m / 3) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, by omega, by omega⟩
  rw [show (3 * q + r) / 3 = q by omega]
  have h := sum_block q
  have h₀ := lucas q 0 (by decide)
  have h₁ := lucas q 1 (by decide)
  have h₂ := lucas q 2 (by decide)
  interval_cases r <;>
    simp only [add_zero, partial_succ, show 3 * q + 2 = 3 * q + 1 + 1 by omega] at * <;>
    omega

private theorem goodCentral (m : ℕ) :
    (¬ 3 ∣ central m) ↔ m % 3 < 2 ∧ ¬ 3 ∣ central (m / 3) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, by omega, by omega⟩
  rw [show (3 * q + r) / 3 = q by omega, show (3 * q + r) % 3 = r by omega]
  have h := lucas q r hr
  interval_cases r <;> omega

private def ternary (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 n)

private theorem ternary_rec (n : ℕ) : ternary n = n % 2 + 3 * ternary (n / 2) := by
  by_cases h : n = 0
  · subst n
    rfl
  · unfold ternary
    nth_rw 1 [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) h]
    rfl

private theorem ternary_strictMono : StrictMono ternary := by
  suffices h : ∀ (j : ℕ), ∀ i < j, ternary i < ternary j from fun i j hij => h j i hij
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro i hij
    rw [ternary_rec i, ternary_rec j]
    obtain hlt | heq := lt_or_eq_of_le (Nat.div_le_div_right (c := 2) hij.le)
    · have ht := ih (j / 2) (by omega) (i / 2) hlt
      omega
    · rw [heq]
      omega

private theorem good_ternary (n : ℕ) : ¬ 3 ∣ central (ternary n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      decide
    · rw [goodCentral, ternary_rec]
      have hm : (n % 2 + 3 * ternary (n / 2)) % 3 = n % 2 := by omega
      have hd : (n % 2 + 3 * ternary (n / 2)) / 3 = ternary (n / 2) := by omega
      rw [hm, hd]
      exact ⟨by omega, ih _ (by omega)⟩

private theorem good_ternary_surj (m : ℕ) : ¬ 3 ∣ central m → ∃ n, ternary n = m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro h
    by_cases hm : m = 0
    · exact ⟨0, by subst m; rfl⟩
    obtain ⟨hr, hq⟩ := (goodCentral m).mp h
    obtain ⟨q, hq'⟩ := ih (m / 3) (by omega) hq
    refine ⟨2 * q + m % 3, ?_⟩
    rw [ternary_rec, show (2 * q + m % 3) % 2 = m % 3 by omega,
      show (2 * q + m % 3) / 2 = q by omega, hq']
    omega

private theorem ternary_eq_sum (n w : ℕ) (hw : n ≤ w) :
    ternary n = ∑ k ∈ range w, 3 ^ k * (n / 2 ^ k % 2) := by
  induction w generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp [ternary]
  | succ w ih =>
    rw [ternary_rec n, sum_range_succ', ih (n / 2) (by omega), Finset.mul_sum]
    simp only [pow_zero, Nat.div_one, one_mul, pow_succ', ← Nat.div_div_eq_div_mul]
    rw [add_comm (n % 2)]
    congr 1
    apply sum_congr rfl
    intro k _
    ring

private def admissible (m : ℕ) : Prop := ¬ 3 ∣ partialSum (m + 1)
private def encoded (n : ℕ) : ℕ := 3 * ternary n

private theorem admissible_iff (m : ℕ) : admissible m ↔ m ∈ Set.range encoded := by
  change (¬ 3 ∣ partialSum (m + 1)) ↔ _
  rw [goodPartial]
  constructor
  · rintro ⟨hr, hq⟩
    obtain ⟨n, hn⟩ := good_ternary_surj _ hq
    refine ⟨n, ?_⟩
    unfold encoded
    rw [hn]
    omega
  · rintro ⟨n, rfl⟩
    unfold encoded
    have hdiv : 3 * ternary n / 3 = ternary n := by omega
    rw [hdiv]
    exact ⟨by omega, good_ternary _⟩

private theorem nth_admissible (n : ℕ) : Nat.nth admissible n = encoded n := by
  have hstrict : StrictMono encoded := fun i j h => Nat.mul_lt_mul_of_pos_left
    (ternary_strictMono h) (by decide)
  have hset : Set.ofPred admissible = Set.range encoded := Set.ext admissible_iff
  have hinf : (Set.ofPred admissible).Infinite := by
    rw [hset]
    exact Set.infinite_range_of_injective hstrict.injective
  have hpred : (fun k => admissible (encoded k)) = (fun _ => True) := by
    funext k
    exact propext ⟨fun _ => trivial, fun _ => (admissible_iff _).mpr ⟨k, rfl⟩⟩
  have h := Nat.nth_comp_of_strictMono (p := admissible) (n := n) hstrict
    (fun k hk => (admissible_iff k).mp hk) (fun hfin => (hinf hfin).elim)
  simpa [hpred] using h.symm

theorem OMA.solution : type_of% @OMA.S_oeis_a081601.main := by
  intro n hn
  change Nat.nth admissible (n - 1) =
    ∑ k ∈ range n, 3 ^ (k + 1) * ((n - 1) / 2 ^ k % 2)
  rw [nth_admissible, encoded, ternary_eq_sum (n - 1) n (Nat.sub_le n 1), Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  rw [pow_succ']
  ring
