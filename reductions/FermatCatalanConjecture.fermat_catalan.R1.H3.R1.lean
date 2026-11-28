import OMAReductions.R_FermatCatalanConjecture_fermat_catalan_R1

/-! Height estimates sufficient for an exponent bound in the odd prime case. -/

open scoped BigOperators

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_R1_H3_R1

private theorem prime_at_least_five {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (hne : p ≠ 3) : 5 ≤ p := by
  by_contra! h
  have h4 : p = 4 := by omega
  exact (show ¬ Nat.Prime 4 by decide) (h4 ▸ hp)

/-- One exponent at least fifteen makes its base contribute at most one
power of the height after taking fifteenth powers. Other bases contribute
at most five powers for a cube or three powers for a higher prime power. -/
private theorem base_product_bound {a e : Fin 3 → ℕ} {i : Fin 3}
    (ha : ∀ j, 0 < a j) (hp : ∀ j, (e j).Prime ∧ 3 ≤ e j) (hi : 15 ≤ e i)
    (hs : a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2) :
    (a 0 * a 1 * a 2) ^ 15 ≤
      (a 2 ^ e 2) ^ (7 + 2 * (Finset.univ.filter (fun j : Fin 3 => e j = 3)).card) := by
  let c := a 2 ^ e 2
  let t (j : Fin 3) : ℕ := if e j = 3 then 1 else 0
  let w (j : Fin 3) : ℕ := (if j = i then 1 else 3) + 2 * t j
  have hle (j : Fin 3) : a j ^ e j ≤ c := by
    fin_cases j
    · change a 0 ^ e 0 ≤ a 2 ^ e 2
      omega
    · change a 1 ^ e 1 ≤ a 2 ^ e 2
      omega
    · exact le_rfl
  have hbase (j : Fin 3) : a j ^ 15 ≤ c ^ w j := by
    by_cases hij : j = i
    · subst j
      have hn : e i ≠ 3 := by omega
      simpa [w, t, hn] using (pow_le_pow_right' (ha i) hi).trans (hle i)
    · by_cases hc : e j = 3
      · have he : a j ^ 15 = (a j ^ e j) ^ 5 := by rw [hc, ← pow_mul]
        rw [he, show w j = 5 by simp [w, t, hij, hc]]
        exact pow_le_pow_left' (hle j) _
      · have h5 := prime_at_least_five (hp j).1 (hp j).2 hc
        have h15 : a j ^ 15 ≤ (a j ^ e j) ^ 3 := by
          rw [← pow_mul]
          exact pow_le_pow_right' (ha j) (by omega)
        rw [show w j = 3 by simp [w, t, hij, hc]]
        exact h15.trans (pow_le_pow_left' (hle j) 3)
  have hw : (∑ j, w j) = 7 + 2 * (Finset.univ.filter (fun j : Fin 3 => e j = 3)).card := by
    unfold w
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hsum : ∀ i : Fin 3, (∑ j : Fin 3, if j = i then (1 : ℕ) else 3) = 7 := by decide
    rw [hsum i]
    simp only [t, Finset.sum_boole, Nat.cast_id]
  calc
    (a 0 * a 1 * a 2) ^ 15 = ∏ j : Fin 3, a j ^ 15 := by simp [Fin.prod_univ_three, mul_pow]
    _ ≤ ∏ j : Fin 3, c ^ w j := Finset.prod_le_prod' (fun j _ => hbase j)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hw]

private theorem height_from_product {C A K m k d s : ℕ} (hC : 0 < C)
    (hAB : A ^ 15 ≤ C ^ d) (hquality : C ^ m ≤ K * A ^ k) (hgap : m * 15 = d * k + s) :
    C ^ s ≤ K ^ 15 := by
  have hprod : C ^ (d * k) * C ^ s ≤ C ^ (d * k) * K ^ 15 := by
    calc
      _ = C ^ (m * 15) := by rw [← pow_add, ← hgap]
      _ ≤ (K * A ^ k) ^ 15 := by simpa only [pow_mul] using pow_le_pow_left' hquality 15
      _ = K ^ 15 * (A ^ 15) ^ k := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 15, pow_mul]
      _ ≤ K ^ 15 * (C ^ d) ^ k := Nat.mul_le_mul_left _ (pow_le_pow_left' hAB _)
      _ = C ^ (d * k) * K ^ 15 := by rw [← pow_mul, mul_comm]
  exact Nat.le_of_mul_le_mul_left hprod (pow_pos hC _)

/-- The height estimate in the case of two cubic exponents. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ (a e : Fin 3 → ℕ) (i : Fin 3),
    (∀ j, 0 < a j) → (a 0).Coprime (a 1) →
    a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2 →
    (∀ j, (e j).Prime ∧ 3 ≤ e j) → 15 ≤ e i → 1 < a i →
    (Finset.univ.filter (fun j : Fin 3 => e j = 3)).card = 2 →
    (a 2 ^ e 2) ^ 3 ≤ K * (a 0 * a 1 * a 2) ^ 4

/-- The height estimate in the case of exactly one cubic exponent. -/
def H2 : Prop :=
  ∃ K : ℕ, ∀ (a e : Fin 3 → ℕ) (i : Fin 3),
    (∀ j, 0 < a j) → (a 0).Coprime (a 1) →
    a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2 →
    (∀ j, (e j).Prime ∧ 3 ≤ e j) → 15 ≤ e i → 1 < a i →
    (Finset.univ.filter (fun j : Fin 3 => e j = 3)).card = 1 →
    (a 2 ^ e 2) ^ 2 ≤ K * (a 0 * a 1 * a 2) ^ 3

/-- The height estimate when the three prime exponents are at least five. -/
def H3 : Prop :=
  ∃ K : ℕ, ∀ (a e : Fin 3 → ℕ) (i : Fin 3),
    (∀ j, 0 < a j) → (a 0).Coprime (a 1) →
    a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2 →
    (∀ j, (e j).Prime ∧ 3 ≤ e j) → 15 ≤ e i → 1 < a i →
    (Finset.univ.filter (fun j : Fin 3 => e j = 3)).card = 0 →
    a 2 ^ e 2 ≤ K * (a 0 * a 1 * a 2) ^ 2

/-- These three estimates suffice for a uniform bound on nonunit exponents. -/
theorem main : H1 → H2 → H3 → OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H3 := by
  intro ⟨K₂,h₂⟩ ⟨K₁,h₁⟩ ⟨K₀,h₀⟩
  refine ⟨14 + K₂ ^ 15 + K₁ ^ 5 + K₀ ^ 15, ?_⟩
  intro v e hv hc heq roots hp i hnon
  by_cases hsmall : e i < 15
  · omega
  have hi : 15 ≤ e i := by omega
  choose a hval using roots
  have ha (j : Fin 3) : 0 < a j := by
    by_contra! hz
    have hvj := hval j
    rw [show a j = 0 by omega, zero_pow (by have := (hp j).2; omega)] at hvj
    exact (hv j).ne hvj
  have hnonA : 1 < a i := by
    by_contra! h
    have hvji := hval i
    rw [show a i = 1 by have := ha i; omega, one_pow] at hvji
    omega
  have hdvd (j : Fin 3) : a j ∣ v j := by
    rw [← hval j]
    exact dvd_pow_self _ (hp j).1.ne_zero
  have hcopA := hc.of_dvd (hdvd 0) (hdvd 1)
  have hsum : a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2 := by simpa only [hval] using heq
  let C := a 2 ^ e 2
  let A := a 0 * a 1 * a 2
  let S := Finset.univ.filter (fun j : Fin 3 => e j = 3)
  have hC : 0 < C := pow_pos (ha 2) _
  have hprod : A ^ 15 ≤ C ^ (7 + 2 * S.card) := base_product_bound ha hp hi hsum
  have hnot : i ∉ S := by simp [S, show e i ≠ 3 by omega]
  have hcard : S.card < 3 := by
    have hS : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun he => hnot (he.symm ▸ Finset.mem_univ i)⟩
    simpa using Finset.card_lt_card hS
  have hvle : v i ≤ C := by
    have hall : ∀ j : Fin 3, v j ≤ v 2 := by
      intro j
      fin_cases j
      · change v 0 ≤ v 2; omega
      · change v 1 ≤ v 2; omega
      · exact le_rfl
    exact (hall i).trans_eq (hval 2).symm
  have heC : e i ≤ C := Nat.lt_two_pow_self.le.trans
    ((pow_le_pow_left' (show 2 ≤ a i by omega) (e i)).trans ((hval i).le.trans hvle))
  obtain hc₀ | hc₁ | hc₂ : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · have hp' : A ^ 15 ≤ C ^ 7 := by simpa [hc₀] using hprod
    have hq : C ^ 1 ≤ K₀ * A ^ 2 := by
      simpa only [pow_one] using h₀ a e i ha hcopA hsum hp hi hnonA hc₀
    have hBound : C ≤ K₀ ^ 15 := by
      simpa only [pow_one] using height_from_product (s := 1) hC hp' hq (by decide)
    omega
  · have hp' : A ^ 15 ≤ C ^ 9 := by simpa [hc₁] using hprod
    have hq := h₁ a e i ha hcopA hsum hp hi hnonA hc₁
    have hBound : C ^ 3 ≤ (K₁ ^ 5) ^ 3 := by
      rw [show (K₁ ^ 5) ^ 3 = K₁ ^ 15 by rw [← pow_mul]]
      exact height_from_product (s := 3) hC hp' hq (by decide)
    have hB : C ≤ K₁ ^ 5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide)).mp hBound
    omega
  · have hp' : A ^ 15 ≤ C ^ 11 := by simpa [hc₂] using hprod
    have hq := h₂ a e i ha hcopA hsum hp hi hnonA hc₂
    have hBound : C ≤ K₂ ^ 15 := by
      simpa only [pow_one] using height_from_product (s := 1) hC hp' hq (by decide)
    omega

/-- A nonexistence theorem for primitive signed sums of cubes supplies the
first estimate, regardless of which term has the large exponent. -/
theorem two_cube_estimate_of_nonexistence
    (exclude : ∀ p : ℕ, p.Prime → 15 ≤ p → ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      x.natAbs.Coprime y.natAbs → x ^ 3 + y ^ 3 = z ^ p → False) : H1 := by
  refine ⟨1, ?_⟩
  intro a e i ha hcop hs hp hi _ hc
  exfalso
  let S := Finset.univ.filter (fun j : Fin 3 => e j = 3)
  have hSi : i ∉ S := by simp [S, show e i ≠ 3 by omega]
  have hsubset : S ⊆ Finset.univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun eq => hSi (eq ▸ hj), Finset.mem_univ _⟩
  have hset : S = Finset.univ.erase i := Finset.eq_of_subset_of_card_le hsubset (by
    have h := Finset.card_erase_add_one (Finset.mem_univ i)
    change S.card = 2 at hc
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega)
  have hcube (j : Fin 3) (hne : j ≠ i) : e j = 3 := by
    have hj : j ∈ S := hset ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    exact (Finset.mem_filter.mp hj).2
  have h10V := (hcop.pow_left (e 0)).pow_right (e 1)
  have h02V : (a 0 ^ e 0).Coprime (a 2 ^ e 2) := hs ▸ Nat.coprime_self_add_right.mpr h10V
  have h12V : (a 1 ^ e 1).Coprime (a 2 ^ e 2) := hs ▸ Nat.coprime_add_self_right.mpr h10V.symm
  have hbase (j : Fin 3) : a j ∣ a j ^ e j := dvd_pow_self _ (hp j).1.ne_zero
  have h02 := h02V.of_dvd (hbase 0) (hbase 2)
  have h12 := h12V.of_dvd (hbase 1) (hbase 2)
  have hpos (j : Fin 3) : (a j : ℤ) ≠ 0 := by exact_mod_cast (ha j).ne'
  have heqZ : (a 0 : ℤ) ^ e 0 + (a 1 : ℤ) ^ e 1 = (a 2 : ℤ) ^ e 2 := by exact_mod_cast hs
  have hprime := (hp i).1
  fin_cases i
  · change (e 0).Prime at hprime
    change 15 ≤ e 0 at hi
    rw [hcube 1 (by decide), hcube 2 (by decide)] at heqZ
    apply exclude (e 0) hprime hi (a 2) (-(a 1 : ℤ)) (a 0)
      (hpos 2) (neg_ne_zero.mpr (hpos 1)) (hpos 0)
    · simpa using h12.symm
    · rw [neg_pow, show (-1 : ℤ) ^ 3 = -1 by decide]
      linarith
  · change (e 1).Prime at hprime
    change 15 ≤ e 1 at hi
    rw [hcube 0 (by decide), hcube 2 (by decide)] at heqZ
    apply exclude (e 1) hprime hi (a 2) (-(a 0 : ℤ)) (a 1)
      (hpos 2) (neg_ne_zero.mpr (hpos 0)) (hpos 1)
    · simpa using h02.symm
    · rw [neg_pow, show (-1 : ℤ) ^ 3 = -1 by decide]
      linarith
  · change (e 2).Prime at hprime
    change 15 ≤ e 2 at hi
    rw [hcube 0 (by decide), hcube 1 (by decide)] at heqZ
    apply exclude (e 2) hprime hi (a 0) (a 1) (a 2) (hpos 0) (hpos 1) (hpos 2)
    · simpa using hcop
    · exact heqZ

/-- With fixed-signature finiteness, the exponent bound also supplies a
uniform height bound on the triples tested by these estimates. -/
theorem uniform_height_of_exponent_bound
    (fixed : OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H1)
    (bounded : OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H3) :
    ∃ B : ℕ, ∀ (a e : Fin 3 → ℕ) (i : Fin 3),
      (∀ j, 0 < a j) → (a 0).Coprime (a 1) →
      a 0 ^ e 0 + a 1 ^ e 1 = a 2 ^ e 2 →
      (∀ j, (e j).Prime ∧ 3 ≤ e j) → 15 ≤ e i → 1 < a i → a 2 ^ e 2 ≤ B := by
  classical
  obtain ⟨P, hP⟩ := bounded
  choose bound hf using OMA.R_FermatCatalanConjecture_fermat_catalan_R1.fixed_height fixed
  let N := max 3 P
  let B := ∑ t : Fin 3 → Fin (N + 1), bound (fun j => (t j : ℕ))
  refine ⟨B, ?_⟩
  intro a e i ha hcop hs hp hlarge hnon
  let v (j : Fin 3) := a j ^ e j
  let f (j : Fin 3) := if a j = 1 then 3 else e j
  have hv (j : Fin 3) : 0 < v j := pow_pos (ha j) _
  have hcv : (v 0).Coprime (v 1) := (hcop.pow_left _).pow_right _
  have hsum : v 0 + v 1 = v 2 := hs
  have hroots (j : Fin 3) : ∃ x : ℕ, x ^ e j = v j := ⟨a j, rfl⟩
  have hfroot (j : Fin 3) : ∃ x : ℕ, x ^ f j = v j := by
    refine ⟨a j, ?_⟩
    by_cases h : a j = 1 <;> simp [f, v, h]
  have h3 (j : Fin 3) : 3 ≤ f j := by
    by_cases h : a j = 1 <;> simp [f, h, (hp j).2]
  have hfhi : 15 ≤ f i := by simpa [f, hnon.ne'] using hlarge
  have hyp := OMA.R_FermatCatalanConjecture_fermat_catalan_R1.hyperbolic_of_large
    (e := f) (fun j => by have := h3 j; omega)
    (fun j _ _ => Or.inl (by have := h3 j; omega)) ⟨i, by omega⟩
  have hfN (j : Fin 3) : f j ≤ N := by
    by_cases hone : a j = 1
    · exact (show f j = 3 by simp [f, hone]) ▸ le_max_left 3 P
    · have htwo : 2 ≤ a j := by have := ha j; omega
      have hbase := pow_le_pow_left' htwo (e j)
      have hdegree := Nat.lt_two_pow_self (n := e j)
      have hvnon : 1 < v j := by
        change 1 < a j ^ e j
        have := (hp j).2
        omega
      have hPj := hP v e hv hcv hsum hroots hp j hvnon
      simpa only [f, if_neg hone, N] using hPj.trans (le_max_right 3 P)
  let t (j : Fin 3) : Fin (N + 1) := ⟨f j, by have := hfN j; omega⟩
  have hle : bound f ≤ B :=
    Finset.single_le_sum (f := fun t : Fin 3 → Fin (N + 1) => bound (fun j => (t j : ℕ)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  exact (hf f v hv hcv hsum (fun j => by have := h3 j; omega) hyp hfroot).trans hle

/-- Darmon–Granville finiteness, expressed by the parent's hypothesis,
makes the three restricted estimates equivalent to the exponent bound. -/
theorem equivalent_given_fixed
    (fixed : OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H1) :
    OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H3 ↔ H1 ∧ H2 ∧ H3 := by
  refine ⟨?_, fun h => main h.1 h.2.1 h.2.2⟩
  intro bounded
  obtain ⟨B, hB⟩ := uniform_height_of_exponent_bound fixed bounded
  refine ⟨⟨B ^ 3, ?_⟩, ⟨B ^ 2, ?_⟩, ⟨B, ?_⟩⟩
  all_goals
    intro a e i ha hcop hs hp hlarge hnon _
    have hc := hB a e i ha hcop hs hp hlarge hnon
    have hA : 0 < a 0 * a 1 * a 2 := Nat.mul_pos (Nat.mul_pos (ha 0) (ha 1)) (ha 2)
  · exact (pow_le_pow_left' hc 3).trans (Nat.le_mul_of_pos_right _ (pow_pos hA 4))
  · exact (pow_le_pow_left' hc 2).trans (Nat.le_mul_of_pos_right _ (pow_pos hA 3))
  · exact hc.trans (Nat.le_mul_of_pos_right _ (pow_pos hA 2))

end OMA.R_FermatCatalanConjecture_fermat_catalan_R1_H3_R1
