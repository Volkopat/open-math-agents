import OMAStatements.S_oeis_a346934
import Mathlib

namespace OMA.P_oeis_a346934

open OMA.S_oeis_a346934

/-- For any odd composite `m ≥ 9` and any `0 ≤ k < m`, `m ∣ k! * (m - 1 - k)!`. -/
private lemma odd_composite_dvd_factorial_mul {m k : ℕ} (hm_odd : Odd m) (hm3 : 3 ≤ m)
    (hnotp : ¬ m.Prime) (hk : k ≤ m - 1) :
    m ∣ k.factorial * (m - 1 - k).factorial := by
  -- Use prime-power divisibility: for every prime `p` with `p ^ e ∣ m` (`e = m.factorization p`),
  -- show `p ^ e ∣ k! * (m - 1 - k)!`, then multiply over all `p ∈ m.primeFactors`!
  have hm0 : m ≠ 0 := by omega
  have hM : (m - 1) / 2 ≤ max k (m - 1 - k) := by omega
  have hM_dvd : (max k (m - 1 - k)).factorial ∣ k.factorial * (m - 1 - k).factorial := by
    rcases le_total k (m - 1 - k) with h | h
    · rw [max_eq_right h]; exact dvd_mul_left _ _
    · rw [max_eq_left h]; exact dvd_mul_right _ _
  -- Helper: if `e * p ≤ M` and `p ≥ 1`, then `p ^ e ∣ M!`!
  have hpe_dvd_fact : ∀ (p e M : ℕ), 1 ≤ p → e * p ≤ M → p ^ e ∣ M.factorial := by
    intro p e M hp hle
    induction e generalizing M with
    | zero => simp
    | succ e ih =>
      have h1 : (e + 1) * p ≤ M := hle
      -- Actually `∏_{j=1}^{e+1} (j * p) = p^(e+1) * (e+1)!` divides `M!`, or use `((e+1)*p)! ∣ M!`!
      suffices hbase : p ^ (e + 1) ∣ ((e + 1) * p).factorial from
        dvd_trans hbase (Nat.factorial_dvd_factorial h1)
      have hprev : p ^ e ∣ (e * p).factorial := ih (e * p) le_rfl
      have hstep : (e * p).factorial * ((e + 1) * p) ∣ ((e + 1) * p).factorial := by
        have hlt : e * p < (e + 1) * p := by nlinarith
        have hsub : (e + 1) * p = ((e + 1) * p - 1) + 1 := by omega
        have hle2 : e * p ≤ (e + 1) * p - 1 := by omega
        rw [hsub, Nat.factorial_succ]
        rw [mul_comm (((e + 1) * p - 1) + 1)]
        exact mul_dvd_mul (Nat.factorial_dvd_factorial hle2) (by rw [← hsub])
      have hmul : p ^ e * ((e + 1) * p) ∣ (e * p).factorial * ((e + 1) * p) :=
        mul_dvd_mul_right hprev _
      have hpow : p ^ (e + 1) ∣ p ^ e * ((e + 1) * p) := by
        rw [pow_succ]
        exact ⟨e + 1, by ring⟩
      exact dvd_trans hpow (dvd_trans hmul hstep)
  -- Check `m = 9` separately!
  by_cases hm9 : m = 9
  · subst hm9
    interval_cases k <;> decide
  -- For all other odd composite `m`, every prime power `p ^ e` dividing `m` divides `(max k (m - 1 - k))!`!
  suffices hpp : ∀ p ∈ m.primeFactors, p ^ (m.factorization p) ∣ k.factorial * (m - 1 - k).factorial by
    rw [← Nat.factorization_le_iff_dvd hm0 (by positivity)]
    intro p
    by_cases hp : p.Prime
    · by_cases hpm : p ∣ m
      · have hdiv := hpp p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩)
        have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (by positivity)).mpr hdiv p
        simpa [hp.factorization_pow] using hle
      · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime m hp]
      exact Nat.zero_le _
  intro p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · exfalso; obtain ⟨t, ht⟩ := hm_odd; obtain ⟨s, hs⟩ := hp_dvd; omega
    · have := hp.two_le; omega
  set e := m.factorization p
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  have hpe_dvd_m : p ^ e ∣ m := Nat.ordProj_dvd m p
  obtain ⟨r, hr⟩ := hpe_dvd_m
  by_cases hr1 : r = 1
  · -- `m = p ^ e` is an odd prime power, composite ⇒ `e ≥ 2`, and `m ≠ 9`!
    subst hr1; simp only [mul_one] at hr
    have he2 : 2 ≤ e := by
      by_contra hlt
      have : e = 1 := by omega
      rw [this, pow_one] at hr
      exact hnotp (hr ▸ hp)
    -- Show `e * p ≤ (m - 1) / 2`!
    have hep_le : e * p ≤ (m - 1) / 2 := by
      -- Need `2 * (e * p) + 1 ≤ p ^ e`!
      suffices h : 2 * (e * p) + 1 ≤ p ^ e by rw [hr]; omega
      by_cases he2_eq : e = 2
      · rw [he2_eq]
        have hp5 : 5 ≤ p := by
          have hp_odd : p % 2 = 1 := by
            rcases hp.eq_two_or_odd with rfl | hodd
            · omega
            · exact hodd
          by_contra hlt
          have : p = 3 := by omega
          subst this; rw [hr, he2_eq] at hm9; norm_num at hm9
        nlinarith
      · have he3 : 3 ≤ e := by omega
        -- Induction on `d ≥ 3`: `2 * (d * p) + 1 ≤ p ^ d` for all `p ≥ 3`!
        have haux : ∀ d : ℕ, 3 ≤ d → 2 * (d * p) + 1 ≤ p ^ d := by
          intro d hd
          induction d, hd using Nat.le_induction with
          | base =>
            have : p ^ 3 = p * p * p := by ring
            nlinarith
          | succ d hd ih =>
            rw [pow_succ]
            have h1 : (2 * (d * p) + 1) * 3 ≤ p ^ d * p := Nat.mul_le_mul ih hp3
            have h2 : 2 * ((d + 1) * p) + 1 ≤ (2 * (d * p) + 1) * 3 := by nlinarith
            exact le_trans h2 h1
        exact haux e he3
    exact dvd_trans (hpe_dvd_fact p e (max k (m - 1 - k)) hp.one_le (le_trans hep_le hM)) hM_dvd
  · -- `r ≠ 1`, and `r` is odd (since `m` is odd), so `r ≥ 3`!
    have hr_odd : Odd r := by
      rcases Nat.even_or_odd r with ⟨t, ht⟩ | h
      · exfalso
        obtain ⟨u, hu⟩ := hm_odd
        have h2 : 2 * (p ^ e * t) = 2 * u + 1 := by
          calc 2 * (p ^ e * t) = p ^ e * (t + t) := by ring
            _ = m := by rw [← ht, ← hr]
            _ = 2 * u + 1 := hu
        omega
      · exact h
    have hr3 : 3 ≤ r := by obtain ⟨t, ht⟩ := hr_odd; omega
    -- Then `p ^ e ≤ m / 3 ≤ (m - 1) / 2 ≤ max k (m - 1 - k)`!
    have hpe_le : p ^ e ≤ (m - 1) / 2 := by
      have h3pe : 3 * p ^ e ≤ m := by rw [hr]; linarith [Nat.mul_le_mul_left (p ^ e) hr3]
      have hpe3 : 3 ≤ p ^ e := le_trans hp3 (Nat.le_self_pow (by omega) p)
      omega
    exact dvd_trans (Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero e hp.ne_zero))
      (le_trans hpe_le hM)) hM_dvd

/-- For any finite type `α`, subset `S : Finset α`, and `g : α → ℤ`,
`S.card! * (Fintype.card α - S.card)!` divides `∑ σ : Equiv.Perm α, ∏ i ∈ S, g (σ i)`. -/
private lemma card_fact_mul_dvd_sum_perm_prod {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℤ) :
    ((S.card.factorial * (m - S.card).factorial : ℕ) : ℤ) ∣
      ∑ σ : Equiv.Perm (Fin m), ∏ i ∈ S, g (σ i) := by
  -- Fiber `σ` by its image `T = S.image σ` in `Finset.univ.powersetCard S.card`!
  have hmem : ∀ σ : Equiv.Perm (Fin m), S.image σ ∈ Finset.univ.powersetCard S.card := by
    intro σ
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, Finset.card_image_of_injective S σ.injective⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin m) => S.image σ)
    (fun σ _ => hmem σ)]
  refine Finset.dvd_sum (fun T hT => ?_)
  rw [Finset.mem_powersetCard] at hT
  -- On the fiber `S.image σ = T`, `∏ i ∈ S, g (σ i) = ∏ j ∈ T, g j` is constant!
  have hconst : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => S.image σ = T),
      ∏ i ∈ S, g (σ i) = ∏ j ∈ T, g j := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2, Finset.prod_image (fun x _ y _ h => σ.injective h)]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- Show the fiber has cardinality `S.card! * (m - S.card)!`!
  suffices hcard : (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => S.image σ = T)).card =
      S.card.factorial * (m - S.card).factorial by
    rw [hcard]; exact dvd_mul_right _ _
  -- Explicit bijection `{σ : Equiv.Perm (Fin m) // S.image σ = T} ≃ ({x // x ∈ S} ≃ {y // y ∈ T}) × ({x // x ∉ S} ≃ {y // y ∉ T})`!
  let e : {σ : Equiv.Perm (Fin m) // S.image σ = T} ≃
      ({x : Fin m // x ∈ S} ≃ {y : Fin m // y ∈ T}) ×
      ({x : Fin m // x ∉ S} ≃ {y : Fin m // y ∉ T}) :=
    { toFun := fun ⟨σ, hσ⟩ =>
        ( { toFun := fun x => ⟨σ x.1, hσ ▸ Finset.mem_image_of_mem σ x.2⟩
            invFun := fun y => ⟨σ.symm y.1, by
              have hy : y.1 ∈ S.image σ := hσ.symm ▸ y.2
              obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
              have : σ.symm y.1 = x := by rw [← hxy, Equiv.symm_apply_apply]
              rwa [this]⟩
            left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.1)
            right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.1) },
          { toFun := fun x => ⟨σ x.1, by
              intro hy
              have hy' : σ x.1 ∈ S.image σ := hσ.symm ▸ hy
              obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hy'
              exact x.2 (σ.injective hzx ▸ hz)⟩
            invFun := fun y => ⟨σ.symm y.1, by
              intro hx
              have : y.1 ∈ S.image σ := by
                rw [Finset.mem_image]
                exact ⟨σ.symm y.1, hx, Equiv.apply_symm_apply σ y.1⟩
              exact y.2 (hσ ▸ this)⟩
            left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.1)
            right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.1) } )
      invFun := fun ⟨e1, e2⟩ =>
        ⟨ (Equiv.sumCompl (· ∈ S)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ T))), by
          ext y
          simp only [Finset.mem_image, Equiv.trans_apply]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have h1 : (Equiv.sumCompl (· ∈ S)).symm x = Sum.inl ⟨x, hx⟩ := by
              simp [Equiv.sumCompl_symm_apply_of_pos hx]
            rw [h1]
            simp
          · intro hy
            refine ⟨(e1.symm ⟨y, hy⟩).1, (e1.symm ⟨y, hy⟩).2, ?_⟩
            have h1 : (Equiv.sumCompl (· ∈ S)).symm (e1.symm ⟨y, hy⟩).1 = Sum.inl (e1.symm ⟨y, hy⟩) := by
              simp [Equiv.sumCompl_symm_apply_of_pos (e1.symm ⟨y, hy⟩).2]
            rw [h1]
            simp ⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        apply Subtype.ext
        ext x
        simp only [Equiv.trans_apply]
        by_cases hx : x ∈ S
        · rw [Equiv.sumCompl_symm_apply_of_pos hx]; simp
        · rw [Equiv.sumCompl_symm_apply_of_neg hx]; simp
      right_inv := by
        rintro ⟨e1, e2⟩
        apply Prod.ext
        · ext x
          simp
        · ext x
          simp }
  have h1 : (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => S.image σ = T)).card =
      Fintype.card {σ : Equiv.Perm (Fin m) // S.image σ = T} :=
    (Fintype.card_subtype _).symm
  rw [h1, Fintype.card_congr e, Fintype.card_prod]
  have hSc : Fintype.card {x : Fin m // x ∈ S} = S.card := Fintype.card_coe S
  have hTc : Fintype.card {y : Fin m // y ∈ T} = S.card := by rw [Fintype.card_coe, hT.2]
  have hSnc : Fintype.card {x : Fin m // x ∉ S} = m - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hTnc : Fintype.card {y : Fin m // y ∉ T} = m - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hT.2]
  have he1 : Fintype.card ({x : Fin m // x ∈ S} ≃ {y : Fin m // y ∈ T}) = S.card.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (hSc.trans hTc.symm)), hSc]
  have he2 : Fintype.card ({x : Fin m // x ∉ S} ≃ {y : Fin m // y ∉ T}) = (m - S.card).factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (hSnc.trans hTnc.symm)), hSnc]
  rw [he1, he2]

private lemma prove_a346934 :
    ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (2 * n + 1) →
      ((2 * n + 1 : ℕ) : ℤ) ∣ permanent (diffMatrix n) := by
  intro n hn hnotp
  -- Expand `∏ i, (f i - g (σ i)) = ∑ S, (∏ i ∈ Sᶜ, f i) * (-1)^|S| * (∏ i ∈ S, g (σ i))`!
  let f : Fin (2 * n) → ℤ := fun i => ((i.val + 1 : ℕ) : ℤ)
  have hexp : permanent (diffMatrix n) =
      ∑ S : Finset (Fin (2 * n)),
        ((-1 : ℤ) ^ S.card * ∏ i ∈ Sᶜ, f i) *
        (∑ σ : Equiv.Perm (Fin (2 * n)), ∏ i ∈ S, f (σ i)) := by
    dsimp [permanent, diffMatrix]
    have hprod : ∀ σ : Equiv.Perm (Fin (2 * n)),
        ∏ i : Fin (2 * n), (f i - f (σ i)) =
        ∑ S : Finset (Fin (2 * n)),
          ((-1 : ℤ) ^ S.card * ∏ i ∈ Sᶜ, f i) * ∏ i ∈ S, f (σ i) := by
      intro σ
      have hsub : ∀ i : Fin (2 * n), f i - f (σ i) = (-f (σ i)) + f i := fun i => by ring
      simp_rw [hsub]
      rw [Fintype.prod_add]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [Finset.prod_neg]
      ring
    change ∑ σ : Equiv.Perm (Fin (2 * n)), ∏ i : Fin (2 * n), (f i - f (σ i)) = _
    simp_rw [hprod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [← Finset.mul_sum]
  rw [hexp]
  refine Finset.dvd_sum (fun S _ => ?_)
  have hk_le : S.card ≤ 2 * n := by
    have := S.card_le_univ
    rwa [Fintype.card_fin] at this
  have h1 : (2 * n + 1) ∣ S.card.factorial * (2 * n - S.card).factorial := by
    have h := odd_composite_dvd_factorial_mul (m := 2 * n + 1) (k := S.card)
      ⟨n, rfl⟩ (by omega) hnotp (by omega)
    rw [show 2 * n + 1 - 1 = 2 * n by omega] at h
    exact h
  have h1z : ((2 * n + 1 : ℕ) : ℤ) ∣ ((S.card.factorial * (2 * n - S.card).factorial : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr h1
  have h2z := card_fact_mul_dvd_sum_perm_prod S f
  exact dvd_mul_of_dvd_right (dvd_trans h1z h2z) _

end OMA.P_oeis_a346934

theorem OMA.solution : type_of% @OMA.S_oeis_a346934.main :=
  OMA.P_oeis_a346934.prove_a346934
