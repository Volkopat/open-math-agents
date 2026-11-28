import OMAStatements.S_arxiv_1810_07219

/-!
Proof of the statement `OMA.S_arxiv_1810_07219.main` (Conjecture 6.0.1 of arXiv 1810.07219).

`A x` is the coefficient of `t^x` in `P x = ∏_j (∑_{k ≠ j} t_k)^(x j)` (each position of block `j`
chooses a letter `k ≠ j`). Adding one copy of the letter `i` multiplies `P x` by `∑_{k ≠ i} t_k`, so
`A (x + e_i)` is at least the coefficient of `t^(x + e_i)` in `t_m * P x`, while `A x` is that
coefficient in `t_i * P x`. It remains to see that `(t_m - t_i) * P x` has a non-negative coefficient
at every monomial whose `i`-exponent is at most its `m`-exponent, when `x i ≤ x m`. Polynomials that
change sign under the exchange of `t_i` and `t_m` and are non-negative below the diagonal (`Good`)
are stable under multiplication by `t_k` (`k ≠ i, m`), by `t_i + t_m` and by `t_i * t_m`; this covers
`(t_m - t_i)` times the part of `P x` that is symmetric in `t_i, t_m`. The remaining factor is a
power of `t_i + (other variables)`, and multiplying by it keeps coefficients non-negative on and
below the diagonal (`Fine`).
-/

namespace OMA.P_arxiv_1810_07219

open OMA.S_arxiv_1810_07219 MvPolynomial

variable {n : ℕ}

/-- `L j = ∑_{k ≠ j} X k`. -/
private noncomputable def L (j : Fin n) : MvPolynomial (Fin n) ℤ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≠ j), X k

/-- `P x = ∏_j (L j)^(x j)`. -/
private noncomputable def P (x : Fin n → ℕ) : MvPolynomial (Fin n) ℤ := ∏ j, L j ^ x j

/-! ### The count as a coefficient -/

private lemma content_iff (x : Fin n → ℕ) (w : (Σ j : Fin n, Fin (x j)) → Fin n) :
    (∑ p, Finsupp.single (w p) 1 = Finsupp.equivFunOnFinite.symm x) ↔
      ∀ k : Fin n, (Finset.univ.filter fun p => w p = k).card = x k := by
  rw [DFunLike.ext_iff]
  refine forall_congr' fun k => ?_
  have h : (∑ p, Finsupp.single (w p) 1 : Fin n →₀ ℕ) k
      = (Finset.univ.filter fun p => w p = k).card := by
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finsupp.single_apply]
  rw [h]
  simp

private lemma A_eq_coeff (x : Fin n → ℕ) :
    (A x : ℤ) = coeff (Finsupp.equivFunOnFinite.symm x) (P x) := by
  classical
  have h1 : P x = ∏ p : (Σ j : Fin n, Fin (x j)),
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ p.1), (X k : MvPolynomial (Fin n) ℤ) := by
    unfold P L
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp
  have h2 : ∀ w : (Σ j : Fin n, Fin (x j)) → Fin n,
      (∏ p, (X (w p) : MvPolynomial (Fin n) ℤ)) = monomial (∑ p, Finsupp.single (w p) 1) 1 := by
    intro w
    rw [monomial_sum_one]
    rfl
  rw [h1, Finset.prod_univ_sum, coeff_sum]
  simp_rw [h2, coeff_monomial]
  rw [Finset.sum_boole]
  unfold A
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [content_iff]

private lemma P_update (x : Fin n → ℕ) (i : Fin n) :
    P (Function.update x i (x i + 1)) = P x * L i := by
  unfold P
  have h : ∀ j, L j ^ (Function.update x i (x i + 1) j) = L j ^ x j * (if j = i then L i else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [pow_succ]
    · simp [hj]
  simp_rw [h, Finset.prod_mul_distrib]
  simp

private lemma toFinsupp_update (x : Fin n → ℕ) (i : Fin n) :
    (Finsupp.equivFunOnFinite.symm (Function.update x i (x i + 1)) : Fin n →₀ ℕ)
      = Finsupp.equivFunOnFinite.symm x + Finsupp.single i 1 := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Function.update_of_ne hk, Ne.symm hk]

/-! ### Polynomials with non-negative coefficients -/

private def NN (Q : MvPolynomial (Fin n) ℤ) : Prop := ∀ μ, 0 ≤ coeff μ Q

private lemma NN_X (k : Fin n) : NN (X k : MvPolynomial (Fin n) ℤ) := by
  classical
  intro μ
  rw [coeff_X]
  split_ifs <;> norm_num

private lemma NN_zero : NN (0 : MvPolynomial (Fin n) ℤ) := by
  intro μ
  simp

private lemma NN_one : NN (1 : MvPolynomial (Fin n) ℤ) := by
  classical
  intro μ
  rw [coeff_one]
  split_ifs <;> norm_num

private lemma NN_add {Q Q' : MvPolynomial (Fin n) ℤ} (h : NN Q) (h' : NN Q') : NN (Q + Q') := by
  intro μ
  rw [coeff_add]
  exact add_nonneg (h μ) (h' μ)

private lemma NN_mul {Q Q' : MvPolynomial (Fin n) ℤ} (h : NN Q) (h' : NN Q') : NN (Q * Q') := by
  classical
  intro μ
  rw [coeff_mul]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (h _) (h' _)

private lemma NN_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℤ)
    (h : ∀ k ∈ s, NN (f k)) : NN (∑ k ∈ s, f k) :=
  Finset.sum_induction f NN (fun _ _ => NN_add) NN_zero h

private lemma NN_pow {Q : MvPolynomial (Fin n) ℤ} (h : NN Q) (e : ℕ) : NN (Q ^ e) := by
  induction e with
  | zero => simpa using NN_one
  | succ e ih => rw [pow_succ]; exact NN_mul ih h

private lemma NN_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℤ)
    (h : ∀ k ∈ s, NN (f k)) : NN (∏ k ∈ s, f k) :=
  Finset.prod_induction f NN (fun _ _ => NN_mul) NN_one h

private lemma NN_L (j : Fin n) : NN (L j) := NN_sum _ _ fun k _ => NN_X k

private lemma NN_P (x : Fin n → ℕ) : NN (P x) := NN_prod _ _ fun j _ => NN_pow (NN_L j) _

/-! ### The sign pattern -/

section signs

variable (i m : Fin n)

/-- `Q` changes sign when the variables `i` and `m` are exchanged. -/
private def Anti (Q : MvPolynomial (Fin n) ℤ) : Prop := rename (Equiv.swap i m) Q = -Q

/-- Antisymmetric, and non-negative at monomials whose `i`-exponent is below the `m`-exponent. -/
private def Good (Q : MvPolynomial (Fin n) ℤ) : Prop :=
  Anti i m Q ∧ ∀ μ : Fin n →₀ ℕ, μ i < μ m → 0 ≤ coeff μ Q

/-- Non-negative at monomials whose `i`-exponent is at most the `m`-exponent. -/
private def Fine (Q : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ μ : Fin n →₀ ℕ, μ i ≤ μ m → 0 ≤ coeff μ Q

/-- The sum of the variables other than `i` and `m`. -/
private noncomputable def rho : MvPolynomial (Fin n) ℤ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ m), X k

variable {i m}

private lemma anti_diag {Q : MvPolynomial (Fin n) ℤ} (h : Anti i m Q) (μ : Fin n →₀ ℕ)
    (hμ : μ i = μ m) : coeff μ Q = 0 := by
  have h1 := coeff_rename_mapDomain (Equiv.swap i m) (Equiv.swap i m).injective Q μ
  have h2 : Finsupp.mapDomain (Equiv.swap i m) μ = μ := by
    ext k
    rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]
    by_cases hk : k = i
    · subst hk
      rw [Equiv.swap_apply_left]
      exact hμ.symm
    · by_cases hk' : k = m
      · subst hk'
        rw [Equiv.swap_apply_right]
        exact hμ
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
  unfold Anti at h
  rw [h2, h, coeff_neg] at h1
  linarith

private lemma fine_of_good {Q : MvPolynomial (Fin n) ℤ} (h : Good i m Q) : Fine i m Q := by
  intro μ hμ
  rcases lt_or_eq_of_le hμ with h1 | h1
  · exact h.2 μ h1
  · rw [anti_diag h.1 μ h1]

private lemma good_zero : Good i m (0 : MvPolynomial (Fin n) ℤ) := by
  refine ⟨?_, fun μ _ => ?_⟩
  · unfold Anti
    simp
  · simp

private lemma good_add {Q Q' : MvPolynomial (Fin n) ℤ} (h : Good i m Q) (h' : Good i m Q') :
    Good i m (Q + Q') := by
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h1 := h.1
    have h2 := h'.1
    unfold Anti at *
    rw [map_add, h1, h2]
    ring
  · rw [coeff_add]
    exact add_nonneg (h.2 μ hμ) (h'.2 μ hμ)

private lemma good_base (him : i ≠ m) : Good i m (X m - X i : MvPolynomial (Fin n) ℤ) := by
  classical
  refine ⟨?_, fun μ hμ => ?_⟩
  · unfold Anti
    rw [map_sub, rename_X, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · rw [coeff_sub, coeff_X, coeff_X]
    have h1 : Finsupp.single i 1 ≠ μ := by
      intro h
      rw [← h] at hμ
      simp [him] at hμ
    rw [if_neg h1]
    split_ifs <;> norm_num

private lemma good_mul_X {k : Fin n} (hki : k ≠ i) (hkm : k ≠ m) {Q : MvPolynomial (Fin n) ℤ}
    (h : Good i m Q) : Good i m (Q * X k) := by
  classical
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h1 := h.1
    unfold Anti at *
    rw [map_mul, h1, rename_X, Equiv.swap_apply_of_ne_of_ne hki hkm]
    ring
  · rw [coeff_mul_X']
    split_ifs with hs
    · apply h.2
      simpa [Finsupp.single_apply, hki, hkm] using hμ
    · exact le_rfl

private lemma good_mul_pair {Q : MvPolynomial (Fin n) ℤ} (h : Good i m Q) :
    Good i m (Q * (X i * X m)) := by
  classical
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h1 := h.1
    unfold Anti at *
    rw [map_mul, map_mul, h1, rename_X, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · rw [← mul_assoc, coeff_mul_X']
    split_ifs with hs
    · rw [coeff_mul_X']
      split_ifs with hs'
      · apply h.2
        rw [Finsupp.mem_support_iff] at hs hs'
        by_cases him : i = m
        · subst him
          exact absurd hμ (lt_irrefl _)
        · have e1 : (μ - Finsupp.single m 1 - Finsupp.single i 1 : Fin n →₀ ℕ) i = μ i - 1 := by
            simp [him]
          have e2 : (μ - Finsupp.single m 1 - Finsupp.single i 1 : Fin n →₀ ℕ) m = μ m - 1 := by
            simp [Ne.symm him]
          have e3 : (μ - Finsupp.single m 1 : Fin n →₀ ℕ) i = μ i := by
            simp [him]
          rw [e3] at hs'
          rw [e1, e2]
          omega
      · exact le_rfl
    · exact le_rfl

private lemma good_mul_sum {Q : MvPolynomial (Fin n) ℤ} (h : Good i m Q) :
    Good i m (Q * (X i + X m)) := by
  classical
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h1 := h.1
    unfold Anti at *
    rw [map_mul, map_add, h1, rename_X, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · have him : i ≠ m := by
      rintro rfl
      exact lt_irrefl _ hμ
    rw [mul_add, coeff_add, coeff_mul_X', coeff_mul_X']
    refine add_nonneg ?_ ?_
    · split_ifs with hs
      · apply h.2
        rw [Finsupp.mem_support_iff] at hs
        have e1 : (μ - Finsupp.single i 1 : Fin n →₀ ℕ) i = μ i - 1 := by simp
        have e2 : (μ - Finsupp.single i 1 : Fin n →₀ ℕ) m = μ m := by
          simp [Ne.symm him]
        rw [e1, e2]
        omega
      · exact le_rfl
    · split_ifs with hs
      · have e1 : (μ - Finsupp.single m 1 : Fin n →₀ ℕ) i = μ i := by
          simp [him]
        have e2 : (μ - Finsupp.single m 1 : Fin n →₀ ℕ) m = μ m - 1 := by simp
        rcases Nat.lt_or_ge (μ i) (μ m - 1) with h1 | h1
        · apply h.2
          rw [e1, e2]
          exact h1
        · have h2 : (μ - Finsupp.single m 1 : Fin n →₀ ℕ) i = (μ - Finsupp.single m 1 : Fin n →₀ ℕ) m := by
            rw [e1, e2]
            omega
          rw [anti_diag h.1 _ h2]
      · exact le_rfl

/-- Multipliers that preserve `Good`. -/
private def GM (i m : Fin n) (F : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ Q, Good i m Q → Good i m (Q * F)

private lemma GM_add {F G : MvPolynomial (Fin n) ℤ} (hF : GM i m F) (hG : GM i m G) :
    GM i m (F + G) := by
  intro Q hQ
  rw [mul_add]
  exact good_add (hF Q hQ) (hG Q hQ)

private lemma GM_mul {F G : MvPolynomial (Fin n) ℤ} (hF : GM i m F) (hG : GM i m G) :
    GM i m (F * G) := by
  intro Q hQ
  rw [← mul_assoc]
  exact hG _ (hF Q hQ)

private lemma GM_zero : GM i m (0 : MvPolynomial (Fin n) ℤ) := by
  intro Q _
  rw [mul_zero]
  exact good_zero

private lemma GM_one : GM i m (1 : MvPolynomial (Fin n) ℤ) := by
  intro Q hQ
  rw [mul_one]
  exact hQ

private lemma GM_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℤ)
    (h : ∀ k ∈ s, GM i m (f k)) : GM i m (∑ k ∈ s, f k) :=
  Finset.sum_induction f (GM i m) (fun _ _ => GM_add) GM_zero h

private lemma GM_pow {F : MvPolynomial (Fin n) ℤ} (hF : GM i m F) (e : ℕ) : GM i m (F ^ e) := by
  induction e with
  | zero => simpa using (GM_one : GM i m (1 : MvPolynomial (Fin n) ℤ))
  | succ e ih => rw [pow_succ]; exact GM_mul ih hF

private lemma GM_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℤ)
    (h : ∀ k ∈ s, GM i m (f k)) : GM i m (∏ k ∈ s, f k) :=
  Finset.prod_induction f (GM i m) (fun _ _ => GM_mul) GM_one h

private lemma GM_rho : GM i m (rho i m) :=
  GM_sum _ _ fun k hk => by
    rw [Finset.mem_filter] at hk
    exact fun Q hQ => good_mul_X hk.2.1 hk.2.2 hQ

private lemma L_i_eq (him : i ≠ m) : L i = X m + rho i m := by
  unfold L rho
  have h : (Finset.univ.filter fun k : Fin n => k ≠ i)
      = insert m (Finset.univ.filter fun k : Fin n => k ≠ i ∧ k ≠ m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      by_cases hkm : k = m
      · exact Or.inl hkm
      · exact Or.inr ⟨hk, hkm⟩
    · rintro (rfl | ⟨hk, _⟩)
      · exact fun h => him h.symm
      · exact hk
  rw [h, Finset.sum_insert (by simp)]

private lemma L_m_eq (him : i ≠ m) : L m = X i + rho i m := by
  unfold L rho
  have h : (Finset.univ.filter fun k : Fin n => k ≠ m)
      = insert i (Finset.univ.filter fun k : Fin n => k ≠ i ∧ k ≠ m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Or.inl hki
      · exact Or.inr ⟨hki, hk⟩
    · rintro (rfl | ⟨_, hk⟩)
      · exact him
      · exact hk
  rw [h, Finset.sum_insert (by simp)]

private lemma L_j_eq (him : i ≠ m) {j : Fin n} (hji : j ≠ i) (hjm : j ≠ m) :
    L j = (X i + X m) + ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ j ∧ k ≠ i ∧ k ≠ m), X k := by
  unfold L
  have h : (Finset.univ.filter fun k : Fin n => k ≠ j)
      = insert i (insert m (Finset.univ.filter fun k : Fin n => k ≠ j ∧ k ≠ i ∧ k ≠ m)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Or.inl hki
      · by_cases hkm : k = m
        · exact Or.inr (Or.inl hkm)
        · exact Or.inr (Or.inr ⟨hk, hki, hkm⟩)
    · rintro (rfl | rfl | ⟨hk, _, _⟩)
      · exact fun h => hji h.symm
      · exact fun h => hjm h.symm
      · exact hk
  rw [h, Finset.sum_insert (by simp [him]), Finset.sum_insert (by simp), add_assoc]

private lemma GM_L_j (him : i ≠ m) {j : Fin n} (hji : j ≠ i) (hjm : j ≠ m) : GM i m (L j) := by
  rw [L_j_eq him hji hjm]
  refine GM_add (fun Q hQ => good_mul_sum hQ) (GM_sum _ _ fun k hk => ?_)
  rw [Finset.mem_filter] at hk
  exact fun Q hQ => good_mul_X hk.2.2.1 hk.2.2.2 hQ

private lemma GM_pair (him : i ≠ m) : GM i m (L i * L m) := by
  rw [L_i_eq him, L_m_eq him]
  have h : (X m + rho i m) * (X i + rho i m)
      = X i * X m + rho i m * (X i + X m) + rho i m * rho i m := by ring
  rw [h]
  exact GM_add (GM_add (fun Q hQ => good_mul_pair hQ)
    (GM_mul GM_rho (fun Q hQ => good_mul_sum hQ))) (GM_mul GM_rho GM_rho)

/-- Multipliers that preserve `Fine`. -/
private def FM (i m : Fin n) (F : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ Q, Fine i m Q → Fine i m (Q * F)

private lemma fine_zero : Fine i m (0 : MvPolynomial (Fin n) ℤ) := by
  intro μ _
  simp

private lemma fine_add {Q Q' : MvPolynomial (Fin n) ℤ} (h : Fine i m Q) (h' : Fine i m Q') :
    Fine i m (Q + Q') := by
  intro μ hμ
  rw [coeff_add]
  exact add_nonneg (h μ hμ) (h' μ hμ)

private lemma FM_add {F G : MvPolynomial (Fin n) ℤ} (hF : FM i m F) (hG : FM i m G) :
    FM i m (F + G) := by
  intro Q hQ
  rw [mul_add]
  exact fine_add (hF Q hQ) (hG Q hQ)

private lemma FM_zero : FM i m (0 : MvPolynomial (Fin n) ℤ) := by
  intro Q _
  rw [mul_zero]
  exact fine_zero

private lemma FM_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℤ)
    (h : ∀ k ∈ s, FM i m (f k)) : FM i m (∑ k ∈ s, f k) :=
  Finset.sum_induction f (FM i m) (fun _ _ => FM_add) FM_zero h

private lemma FM_pow {F : MvPolynomial (Fin n) ℤ} (hF : FM i m F) (e : ℕ) : FM i m (F ^ e) := by
  induction e with
  | zero =>
    intro Q hQ
    simpa using hQ
  | succ e ih =>
    intro Q hQ
    rw [pow_succ, ← mul_assoc]
    exact hF _ (ih Q hQ)

private lemma FM_X {k : Fin n} (hki : k ≠ i) (hkm : k ≠ m) : FM i m (X k) := by
  classical
  intro Q hQ μ hμ
  rw [coeff_mul_X']
  split_ifs with hs
  · apply hQ
    simpa [Finsupp.single_apply, hki, hkm] using hμ
  · exact le_rfl

private lemma FM_Xi (him : i ≠ m) : FM i m (X i) := by
  classical
  intro Q hQ μ hμ
  rw [coeff_mul_X']
  split_ifs with hs
  · apply hQ
    have e1 : (μ - Finsupp.single i 1 : Fin n →₀ ℕ) i = μ i - 1 := by simp
    have e2 : (μ - Finsupp.single i 1 : Fin n →₀ ℕ) m = μ m := by
      simp [Ne.symm him]
    rw [e1, e2]
    omega
  · exact le_rfl

private lemma FM_L_m (him : i ≠ m) : FM i m (L m) := by
  rw [L_m_eq him]
  refine FM_add (FM_Xi him) (FM_sum _ _ fun k hk => ?_)
  rw [Finset.mem_filter] at hk
  exact FM_X hk.2.1 hk.2.2

private lemma P_split (him : i ≠ m) (x : Fin n → ℕ) (hx : x i ≤ x m) :
    P x = (L i * L m) ^ x i
      * (∏ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i ∧ j ≠ m), L j ^ x j)
      * L m ^ (x m - x i) := by
  unfold P
  have hU : (Finset.univ : Finset (Fin n))
      = insert i (insert m (Finset.univ.filter fun j : Fin n => j ≠ i ∧ j ≠ m)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro _
      by_cases hji : j = i
      · exact Or.inl hji
      · by_cases hjm : j = m
        · exact Or.inr (Or.inl hjm)
        · exact Or.inr (Or.inr ⟨hji, hjm⟩)
    · intro _
      trivial
  obtain ⟨d, hd⟩ : ∃ d, x m = x i + d := ⟨x m - x i, by omega⟩
  conv_lhs => rw [hU]
  rw [Finset.prod_insert (by simp [him]), Finset.prod_insert (by simp), hd, Nat.add_sub_cancel_left,
    pow_add, mul_pow]
  ring

private lemma fine_main (him : i ≠ m) (x : Fin n → ℕ) (hx : x i ≤ x m) :
    Fine i m ((X m - X i) * P x) := by
  rw [P_split him x hx]
  have hgood : Good i m ((X m - X i) * ((L i * L m) ^ x i
      * ∏ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i ∧ j ≠ m), L j ^ x j)) := by
    refine GM_mul (GM_pow (GM_pair him) _) (GM_prod _ _ fun j hj => ?_) _ (good_base him)
    rw [Finset.mem_filter] at hj
    exact GM_pow (GM_L_j him hj.2.1 hj.2.2) _
  have h : (X m - X i) * ((L i * L m) ^ x i
      * (∏ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i ∧ j ≠ m), L j ^ x j) * L m ^ (x m - x i))
      = ((X m - X i) * ((L i * L m) ^ x i
      * ∏ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i ∧ j ≠ m), L j ^ x j)) * L m ^ (x m - x i) := by
    ring
  rw [h]
  exact FM_pow (FM_L_m him) _ _ (fine_of_good hgood)

end signs

theorem prove_main : ∀ (n : ℕ) (x : Fin n → ℕ) (i : Fin n), (∃ m : Fin n, x i < x m) →
    A x ≤ A (Function.update x i (x i + 1)) := by
  classical
  intro n x i ⟨m, hm⟩
  have him : i ≠ m := by
    rintro rfl
    exact lt_irrefl _ hm
  have hA := A_eq_coeff x
  have hA' := A_eq_coeff (Function.update x i (x i + 1))
  rw [P_update, toFinsupp_update, L_i_eq him, mul_add, coeff_add] at hA'
  set μ : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm x + Finsupp.single i 1 with hμ
  have h2 : 0 ≤ coeff μ (P x * rho i m) :=
    NN_mul (NN_P x) (NN_sum _ _ fun k _ => NN_X k) μ
  have hμim : μ i ≤ μ m := by
    simp [hμ, Ne.symm him]
    omega
  have h3 : 0 ≤ coeff μ ((X m - X i) * P x) := fine_main him x hm.le μ hμim
  have h4 : coeff μ ((X m - X i) * P x) = coeff μ (P x * X m) - coeff μ (P x * X i) := by
    rw [sub_mul, coeff_sub, mul_comm (X m), mul_comm (X i)]
  have h5 : coeff μ (P x * X i) = coeff (Finsupp.equivFunOnFinite.symm x) (P x) :=
    coeff_mul_X _ _ _
  have h6 : (A x : ℤ) ≤ A (Function.update x i (x i + 1)) := by
    rw [hA, hA']
    linarith
  exact_mod_cast h6

end OMA.P_arxiv_1810_07219

theorem OMA.solution : type_of% @OMA.S_arxiv_1810_07219.main :=
  OMA.P_arxiv_1810_07219.prove_main
