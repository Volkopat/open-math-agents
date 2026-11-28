import FormalConjectures.Wikipedia.FermatCatalanConjecture

/-! Fixed signatures and bounds on prime exponents of nonunit powers imply Fermat–Catalan finiteness. -/

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_R1

def H1 : Prop :=
  ∀ m n k : ℕ, 0 < m → 0 < n → 0 < k → (1 / m : ℝ) + 1 / n + 1 / k < 1 →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ m + b ^ n = c ^ k ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime}.Finite

def H2 : Prop :=
  ∃ P : ℕ, ∀ v e : Fin 3 → ℕ,
    (∀ i, 0 < v i) → (v 0).Coprime (v 1) → v 0 + v 1 = v 2 →
    (∀ i, ∃ a : ℕ, a ^ e i = v i) →
    (∀ i, (e i).Prime ∨ e i = 4) → (∃! i, e i = 2) →
    ∀ i, 1 < v i → e i ≤ P

def H3 : Prop :=
  ∃ P : ℕ, ∀ v e : Fin 3 → ℕ,
    (∀ i, 0 < v i) → (v 0).Coprime (v 1) → v 0 + v 1 = v 2 →
    (∀ i, ∃ a : ℕ, a ^ e i = v i) →
    (∀ i, (e i).Prime ∧ 3 ≤ e i) →
    ∀ i, 1 < v i → e i ≤ P

lemma fixed_height (fixed : H1) :
  ∀ e : Fin 3 → ℕ, ∃ B : ℕ, ∀ v : Fin 3 → ℕ,
    (∀ i, 0 < v i) → (v 0).Coprime (v 1) → v 0 + v 1 = v 2 →
    (∀ i, 2 ≤ e i) → (∑ i, (1 / e i : ℝ)) < 1 →
    (∀ i, ∃ a : ℕ, a ^ e i = v i) → v 2 ≤ B := by
  intro e
  by_cases valid : (∀ i, 2 ≤ e i) ∧ (∑ i, (1 / e i : ℝ)) < 1
  · have pos (i) : 0 < e i := lt_of_lt_of_le (by decide : 0 < 2) (valid.1 i)
    have finite := fixed (e 0) (e 1) (e 2) (pos _) (pos _) (pos _)
      (by simpa only [Fin.sum_univ_three] using valid.2)
    obtain ⟨B, upper⟩ := (finite.image (fun t : ℕ × ℕ × ℕ => t.2.2 ^ e 2)).exists_le
    refine ⟨B, fun v hv coprime eqn _ _ roots => ?_⟩
    choose a pow_eq using roots
    have base_pos (i) : 0 < a i := by
      by_contra! zero
      have ha : a i = 0 := by omega
      have hp := pow_eq i
      rw [ha, zero_pow (pos i).ne'] at hp
      exact (hv i).ne hp
    have dvd (i) : a i ∣ v i := pow_eq i ▸ dvd_pow_self (a i) (pos i).ne'
    have h01 := coprime.of_dvd (dvd 0) (dvd 1)
    have h02 : (a 0).Coprime (a 2) := Nat.Coprime.of_dvd (dvd 0) (dvd 2)
      (eqn ▸ Nat.coprime_self_add_right.mpr coprime)
    have h12 : (a 1).Coprime (a 2) := Nat.Coprime.of_dvd (dvd 1) (dvd 2)
      (eqn ▸ Nat.coprime_add_self_right.mpr coprime.symm)
    apply upper
    refine ⟨(a 0, a 1, a 2), ⟨base_pos 0, base_pos 1, base_pos 2, ?_, ?_⟩, pow_eq 2⟩
    · simpa only [pow_eq] using eqn
    · intro x hx y hy hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact (hne rfl).elim | assumption | exact h01.symm | exact h02.symm | exact h12.symm
  · exact ⟨0, fun _ _ _ _ lo hyp _ => (valid ⟨lo, hyp⟩).elim⟩

lemma proper_divisor {n t : ℕ} (hn : 2 ≤ n) (hsize : t * t < n)
    (hcomp : ¬ n.Prime) : ∃ d, t < d ∧ d < n ∧ d ∣ n := by
  obtain ⟨a, ⟨b, hab⟩, ha, han⟩ := Nat.exists_dvd_of_not_prime2 hn hcomp
  by_cases h : t < a
  · exact ⟨a, h, han, b, hab⟩
  · have hb : t < b := by
      by_contra! hb
      exact hsize.not_ge (hab ▸ Nat.mul_le_mul (by omega) hb)
    exact ⟨b, hb, by nlinarith, a, by simpa [mul_comm] using hab⟩

lemma root_of_divisor {v e d : ℕ} (h : ∃ a : ℕ, a ^ e = v) (hd : d ∣ e) :
    ∃ a : ℕ, a ^ d = v := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨t, rfl⟩ := hd
  exact ⟨a ^ t, by rw [← pow_mul, mul_comm t d]⟩

lemma at_most_one_two {e : Fin 3 → ℕ} (h : (∑ i, (1 / e i : ℝ)) < 1)
    (i j : Fin 3) (hne : i ≠ j) : e i ≠ 2 ∨ e j ≠ 2 := by
  by_contra! he
  have bounded := Finset.sum_le_univ_sum_of_nonneg (s := {i, j})
    (fun k : Fin 3 => show (0 : ℝ) ≤ 1 / e k by positivity)
  simp [hne, he.1, he.2] at bounded
  simp only [one_div] at h
  linarith only [bounded, h]

lemma hyperbolic_of_large {e : Fin 3 → ℕ} (lo : ∀ i, 2 ≤ e i)
    (two : ∀ i j, i ≠ j → e i ≠ 2 ∨ e j ≠ 2)
    (large : ∃ i, 7 ≤ e i) : (∑ i, (1 / e i : ℝ)) < 1 := by
  have inverse_bound (i : Fin 3) (t : ℕ) (ht : 0 < t) (hle : t ≤ e i) :
      (1 / e i : ℝ) ≤ 1 / t :=
    one_div_le_one_div_of_le (by exact_mod_cast ht) (by exact_mod_cast hle)
  have pair (j k : Fin 3) (hjk : j ≠ k) :
      (1 / e j : ℝ) + 1 / e k ≤ 1 / 2 + 1 / 3 := by
    rcases two j k hjk with hj | hk
    · linarith only [inverse_bound j 3 (by decide) (by have := lo j; omega),
        inverse_bound k 2 (by decide) (lo k)]
    · linarith only [inverse_bound j 2 (by decide) (lo j),
        inverse_bound k 3 (by decide) (by have := lo k; omega)]
  obtain ⟨i, hi⟩ := large
  have h := inverse_bound i 7 (by decide) hi
  rw [Fin.sum_univ_three]
  fin_cases i
  · change (1 / e 0 : ℝ) ≤ 1 / 7 at h
    linarith only [h, pair 1 2 (by decide)]
  · change (1 / e 1 : ℝ) ≤ 1 / 7 at h
    linarith only [h, pair 0 2 (by decide)]
  · change (1 / e 2 : ℝ) ≤ 1 / 7 at h
    linarith only [h, pair 0 1 (by decide)]

lemma minimal_signature {v : Fin 3 → ℕ} (hv : ∀ i, 0 < v i)
    (seed : ∃ e : Fin 3 → ℕ, (∀ i, 2 ≤ e i) ∧ (∑ i, (1 / e i : ℝ)) < 1 ∧
      ∀ i, ∃ a : ℕ, a ^ e i = v i) :
    ∃ e : Fin 3 → ℕ, (∀ i, 2 ≤ e i) ∧ (∑ i, (1 / e i : ℝ)) < 1 ∧
      (∀ i, ∃ a : ℕ, a ^ e i = v i) ∧ (∀ i, 7 < e i → 1 < v i) ∧
      ((∀ i, e i ≤ 36) ∨
       ((∀ i, (e i).Prime ∨ e i = 4) ∧ (∃! i, e i = 2)) ∨
       (∀ i, (e i).Prime ∧ 3 ≤ e i)) := by
  classical
  let admissible (e : Fin 3 → ℕ) := (∀ i, 2 ≤ e i) ∧
    (∑ i, (1 / e i : ℝ)) < 1 ∧ ∀ i, ∃ a : ℕ, a ^ e i = v i
  obtain ⟨e, emin⟩ := exists_minimalFor_of_wellFoundedLT admissible (fun e => ∑ i, e i) seed
  obtain ⟨lo, hyp, roots⟩ := emin.1
  have two := at_most_one_two hyp
  have cannot (i : Fin 3) (d : ℕ) (hd : 2 ≤ d) (drop : d < e i)
      (root : ∃ a : ℕ, a ^ d = v i)
      (safe : 3 ≤ d ∨ ∀ j, j ≠ i → e j ≠ 2)
      (large : ∃ j, 7 ≤ Function.update e i d j) : False := by
    have lo' (j) : 2 ≤ Function.update e i d j := by
      by_cases hj : j = i <;> simp [hj, hd, lo]
    have two' (j k : Fin 3) (hjk : j ≠ k) :
        Function.update e i d j ≠ 2 ∨ Function.update e i d k ≠ 2 := by
      rcases safe with larger | unique
      · have hne : d ≠ 2 := by omega
        by_cases hj : j = i <;> by_cases hk : k = i <;>
          simp_all [Function.update_apply]
      · by_cases hj : j = i <;> by_cases hk : k = i <;>
          simp_all [Function.update_apply]
    have admissible' : admissible (Function.update e i d) := by
      refine ⟨lo', hyperbolic_of_large lo' two' large, fun j => ?_⟩
      by_cases hj : j = i
      · subst j; simpa using root
      · simpa [Function.update_of_ne hj] using roots j
    have smaller : (∑ j, Function.update e i d j) < ∑ j, e j := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hj : j = i
        · subst j; simpa using drop.le
        · simp [Function.update_of_ne hj]
      · exact ⟨i, Finset.mem_univ _, by simpa using drop⟩
    exact smaller.not_ge (emin.le_of_le admissible' smaller.le)
  have unit (i) (hi : 7 < e i) : 1 < v i := by
    by_contra! h
    have h1 : v i = 1 := by have := hv i; omega
    exact cannot i 7 (by decide) hi ⟨1, by simp [h1]⟩ (Or.inl (by decide)) ⟨i, by simp⟩
  refine ⟨e, lo, hyp, roots, unit, ?_⟩
  by_cases small : ∀ i, e i ≤ 36
  · exact Or.inl small
  push Not at small
  obtain ⟨k, hk⟩ := small
  have pk : (e k).Prime := by
    by_contra composite
    obtain ⟨d, hd, drop, dvd⟩ := proper_divisor (t := 6) (lo k) (by omega) composite
    exact cannot k d (by omega) drop (root_of_divisor (roots k) dvd)
      (Or.inl (by omega)) ⟨k, by rw [Function.update_self]; omega⟩
  have normal (i) : (e i).Prime ∨ e i = 4 := by
    by_contra! bad
    have bigger : 4 < e i := by
      have he := lo i
      have h₂ : e i ≠ 2 := fun h => bad.1 (h ▸ Nat.prime_two)
      have h₃ : e i ≠ 3 := fun h => bad.1 (h ▸ Nat.prime_three)
      omega
    obtain ⟨d, hd, drop, dvd⟩ := proper_divisor (t := 2) (lo i) (by omega) bad.1
    have hki : k ≠ i := fun h => bad.1 (h ▸ pk)
    exact cannot i d (by omega) drop (root_of_divisor (roots i) dvd)
      (Or.inl hd) ⟨k, by rw [Function.update_of_ne hki]; omega⟩
  right
  by_cases square : ∃ i, e i = 2
  · obtain ⟨i, hi⟩ := square
    refine Or.inl ⟨normal, i, hi, fun j hj => ?_⟩
    by_contra hji
    exact (two j i hji).elim (fun h => h hj) (fun h => h hi)
  · push Not at square
    refine Or.inr fun i => ⟨?_, by have := lo i; have := square i; omega⟩
    rcases normal i with prime | four
    · exact prime
    · have hki : k ≠ i := by rintro rfl; omega
      exact (cannot i 2 (by decide) (by omega) (root_of_divisor (roots i) (by simp [four]))
        (Or.inr (fun j _ => square j)) ⟨k, by rw [Function.update_of_ne hki]; omega⟩).elim

theorem main : H1 → H2 → H3 → type_of% @FermatCatalanConjecture.fermat_catalan := by
  classical
  intro fixed ⟨P, square⟩ ⟨Q, odd⟩
  choose bound fixed_bound using fixed_height fixed
  let N := max 36 (max P Q)
  let B := ∑ s : Fin 3 → Fin (N + 1), bound (fun i => (s i : ℕ))
  apply ((Set.finite_Iic B).prod ((Set.finite_Iic B).prod (Set.finite_Iic B))).subset
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨positive, coprime, eqn, reciprocal⟩ := hf
  let v : Fin 3 → ℕ := ![f 0 ^ f 3, f 1 ^ f 4, f 2 ^ f 5]
  let e₀ : Fin 3 → ℕ := ![f 3, f 4, f 5]
  have hv : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> exact pow_pos (positive _) _
  have hc : (v 0).Coprime (v 1) :=
    ((coprime (by simp : (0 : Fin 6) ∈ _) (by simp : (1 : Fin 6) ∈ _)
      (by decide : (0 : Fin 6) ≠ 1)).pow_left _).pow_right _
  have heq : v 0 + v 1 = v 2 := eqn
  have window : (Finset.Icc (3 : Fin 6) 5) = {3, 4, 5} := by decide
  have sum₀ : (∑ i, (1 / e₀ i : ℝ)) < 1 := by
    simpa [window, Fin.sum_univ_three, e₀, add_assoc] using reciprocal
  have lo₀ (i) : 2 ≤ e₀ i := by
    have pos : 0 < e₀ i := by fin_cases i <;> exact positive _
    have term := Finset.single_le_sum (f := fun j => (1 / e₀ j : ℝ))
      (fun j _ => by positivity) (Finset.mem_univ i)
    by_contra! h
    have he : e₀ i = 1 := by omega
    exact sum₀.not_ge (by simpa only [he, Nat.cast_one, div_one] using term)
  have roots₀ (i) : ∃ a : ℕ, a ^ e₀ i = v i := by
    fin_cases i
    · exact ⟨f 0, rfl⟩
    · exact ⟨f 1, rfl⟩
    · exact ⟨f 2, rfl⟩
  obtain ⟨e, lo, hyp, roots, units, shape⟩ := minimal_signature hv ⟨e₀, lo₀, sum₀, roots₀⟩
  have leN (i) : e i ≤ N := by
    by_cases small : e i ≤ 36
    · exact small.trans (le_max_left ..)
    have nonunit := units i (by omega)
    rcases shape with allsmall | ⟨normal, hasSquare⟩ | primes
    · exact (allsmall i).trans (le_max_left ..)
    · exact (square v e hv hc heq roots normal hasSquare i nonunit).trans
        ((le_max_left P Q).trans (le_max_right ..))
    · exact (odd v e hv hc heq roots primes i nonunit).trans
        ((le_max_right P Q).trans (le_max_right ..))
  let s (i) : Fin (N + 1) := ⟨e i, Nat.lt_succ_of_le (leN i)⟩
  have leB : bound e ≤ B :=
    Finset.single_le_sum (f := fun t : Fin 3 → Fin (N + 1) => bound (fun i => (t i : ℕ)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have height := (fixed_bound e v hv hc heq lo hyp roots).trans leB
  change v 0 ≤ B ∧ v 1 ≤ B ∧ v 2 ≤ B
  omega

end OMA.R_FermatCatalanConjecture_fermat_catalan_R1
