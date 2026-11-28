import OMAReductions.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1

-- Credit: @grp06
/-!
Fixed-width finiteness for odd integers of fixed abundancy.
The integer-abundancy result is due to Chen and Luo, Theorem 1
(https://doi.org/10.1017/S0004972711002462).
Nielsen, Theorem 1, gives bounds for fixed rational abundancy
(https://zenodo.org/records/7607545).

The divisor-sum factorization below follows physbuzz's `local_ratio` and
`ratio_factors` in the Erdős 470 reduction
`Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1`
(https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12742).
-/

open Filter Finset
open scoped Topology BigOperators ArithmeticFunction.sigma

namespace OMA.Erdos1053FixedWidth

private theorem nat_subsequence (u : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ c, ∀ m, u (φ m) = c) ∨ Tendsto (u ∘ φ) atTop atTop) := by
  classical
  by_cases h : ∃ c, ∃ᶠ m in atTop, u m = c
  · obtain ⟨c, hc⟩ := h
    obtain ⟨φ, hφ, heq⟩ := extraction_of_frequently_atTop hc
    exact ⟨φ, hφ, Or.inl ⟨c, heq⟩⟩
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    apply tendsto_atTop.2
    intro b
    have hb : ∀ᶠ m in atTop, ∀ c ∈ range b, u m ≠ c :=
      (Filter.eventually_all_finset (range b)).2
        (fun c _ => Filter.not_frequently.mp (fun hc => h ⟨c, hc⟩))
    filter_upwards [hb] with m hm
    exact le_of_not_gt fun hlt => hm (u m) (mem_range.mpr hlt) rfl

private def Classified (u : ℕ → ℕ × ℕ) : Prop :=
  (∃ x, ∀ m, u m = x) ∨
  Tendsto (fun m => (u m).1) atTop atTop ∨
  (∃ p, (∀ m, (u m).1 = p) ∧ Tendsto (fun m => (u m).2) atTop atTop)

private theorem Classified.comp {u : ℕ → ℕ × ℕ} (h : Classified u)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : Classified (u ∘ φ) := by
  rcases h with ⟨x, hx⟩ | hp | ⟨p, hp, ha⟩
  · exact Or.inl ⟨x, fun m => hx (φ m)⟩
  · exact Or.inr (Or.inl (hp.comp hφ.tendsto_atTop))
  · exact Or.inr (Or.inr ⟨p, fun m => hp (φ m), ha.comp hφ.tendsto_atTop⟩)

private theorem pair_subsequence (u : ℕ → ℕ × ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Classified (u ∘ φ) := by
  obtain ⟨φ, hφ, h⟩ := nat_subsequence (fun m => (u m).1)
  rcases h with ⟨p, hp⟩ | hp
  · obtain ⟨ψ, hψ, h⟩ := nat_subsequence (fun m => (u (φ m)).2)
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    rcases h with ⟨a, ha⟩ | ha
    · exact Or.inl ⟨(p, a), fun m => Prod.ext (hp (ψ m)) (ha m)⟩
    · exact Or.inr (Or.inr ⟨p, fun m => hp (ψ m), ha⟩)
  · exact ⟨φ, hφ, Or.inr (Or.inl hp)⟩

private theorem tuple_subsequence (r : ℕ) (u : ℕ → Fin r → ℕ × ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, Classified (fun m => u (φ m) i) := by
  induction r with
  | zero =>
    exact ⟨id, strictMono_id, fun i => Fin.elim0 i⟩
  | succ r ih =>
    obtain ⟨φ, hφ, hh⟩ := pair_subsequence (fun m => u m 0)
    obtain ⟨ψ, hψ, ht⟩ := ih (fun m i => u (φ m) i.succ)
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ht j) i
    exact hh.comp hψ

private noncomputable def abundance (n : ℕ) : ℝ :=
  (σ 1 n : ℝ) / (n : ℝ)

private noncomputable def localRatio (x : ℕ × ℕ) : ℝ :=
  abundance (x.1 ^ x.2)

private theorem localRatio_sum {p a : ℕ} (hp : p.Prime) :
    localRatio (p, a) = (∑ j ∈ range (a + 1), (p : ℝ)^j) / (p : ℝ)^a := by
  simp only [localRatio, abundance, ArithmeticFunction.sigma_one_apply_prime_pow hp,
    Nat.cast_sum, Nat.cast_pow]

private theorem abundance_factors {n : ℕ} (hn : n ≠ 0) :
    abundance n = ∏ p ∈ n.primeFactors, localRatio (p, n.factorization p) := by
  have hs : (σ 1 n : ℝ) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p + 1), (p : ℝ)^j := by
    rw [ArithmeticFunction.sigma_one_apply]
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_divisors hn)
  have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ)^n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  calc
    abundance n = (σ 1 n : ℝ) / (n : ℝ) := rfl
    _ = _ := by
      rw [hs, hn', ← prod_div_distrib]
      exact Finset.prod_congr rfl (fun p hp => (localRatio_sum (Nat.prime_of_mem_primeFactors hp)).symm)

private def Valid (x : ℕ × ℕ) : Prop :=
  x.1.Prime ∧ Odd x.1 ∧ 0 < x.2

private theorem localRatio_closed {p a : ℕ} (hp : p.Prime) :
    localRatio (p, a) = ((p : ℝ) - ((p : ℝ)^a)⁻¹) / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow := (pow_pos hp0 a).ne'
  rw [localRatio_sum hp]
  apply (div_eq_div_iff hpow (sub_pos.mpr hp1).ne').2
  rw [geom_sum_mul, pow_succ, sub_mul, inv_mul_cancel₀ hpow, mul_comm ((p : ℝ)^a)]

private theorem one_lt_localRatio {x : ℕ × ℕ} (hx : Valid x) :
    1 < localRatio x := by
  obtain ⟨p, a⟩ := x
  obtain ⟨hp, _, ha⟩ := hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (((p : ℝ)^a)⁻¹) < 1 :=
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (Nat.ne_of_gt ha))
  rw [localRatio_closed hp, lt_div_iff₀ (sub_pos.mpr hp1), one_mul]
  linarith

private theorem localRatio_upper {x : ℕ × ℕ} (hx : Valid x) :
    localRatio x ≤ 1 + ((x.1 : ℝ) - 1)⁻¹ := by
  obtain ⟨p, a⟩ := x
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hx.1.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hsub := sub_pos.mpr hp1
  change localRatio (p, a) ≤ 1 + ((p : ℝ) - 1)⁻¹
  rw [localRatio_closed hx.1, div_le_iff₀ hsub, add_mul, one_mul, inv_mul_cancel₀ hsub.ne']
  linarith [inv_nonneg.mpr (pow_pos hp0 a).le]

private theorem limit_large_prime {u : ℕ → ℕ × ℕ} (hu : ∀ m, Valid (u m))
    (hp : Tendsto (fun m => (u m).1) atTop atTop) :
    Tendsto (fun m => localRatio (u m)) atTop (𝓝 1) := by
  have hcast : Tendsto (fun m => ((u m).1 : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  have hsub : Tendsto (fun m => ((u m).1 : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hcast
  have hinv : Tendsto (fun m => (((u m).1 : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
    hsub.inv_tendsto_atTop
  have hupper : Tendsto (fun m => 1 + (((u m).1 : ℝ) - 1)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun m => (one_lt_localRatio (hu m)).le) (fun m => localRatio_upper (hu m))

private theorem limit_large_exponent {u : ℕ → ℕ × ℕ} {p : ℕ} (hp : p.Prime)
    (hfixed : ∀ m, (u m).1 = p) (ha : Tendsto (fun m => (u m).2) atTop atTop) :
    Tendsto (fun m => localRatio (u m)) atTop (𝓝 ((p : ℝ) / ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : Tendsto (fun m => (p : ℝ)^(u m).2) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp1).comp ha
  have hinv : Tendsto (fun m => ((p : ℝ)^(u m).2)⁻¹) atTop (𝓝 0) :=
    hpow.inv_tendsto_atTop
  have ht : Tendsto (fun m => ((p : ℝ) - ((p : ℝ)^(u m).2)⁻¹) / ((p : ℝ) - 1))
      atTop (𝓝 ((p : ℝ) / ((p : ℝ) - 1))) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (p : ℝ))).sub hinv).div_const ((p : ℝ) - 1)
  apply ht.congr
  intro m
  have heq : u m = (p, (u m).2) := Prod.ext (hfixed m) rfl
  calc
    _ = localRatio (p, (u m).2) := (localRatio_closed hp).symm
    _ = localRatio (u m) := congrArg localRatio heq.symm

/-- The limiting factors have an odd numerator, and the ones different from one
have an even denominator. -/
private theorem coordinate_limit {u : ℕ → ℕ × ℕ} (hu : ∀ m, Valid (u m)) (h : Classified u)
    (hnc : ¬ ∃ x, ∀ m, u m = x) :
    ∃ b d : ℕ, Odd b ∧ 0 < d ∧
      ((b : ℝ) / d = 1 ∨ Even d) ∧
      Tendsto (fun m => localRatio (u m)) atTop (𝓝 ((b : ℝ) / d)) := by
  rcases h.resolve_left hnc with hp | ⟨p, hp, ha⟩
  · exact ⟨1, 1, by decide, by decide, Or.inl (by norm_num),
      by simpa using limit_large_prime hu hp⟩
  · have hv : p.Prime ∧ Odd p := by
      have h0 := hu 0
      rw [← hp 0]
      exact ⟨h0.1, h0.2.1⟩
    have hp1 : 1 < p := hv.1.one_lt
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp1.le, Nat.cast_one]
    refine ⟨p, p - 1, hv.2, by omega, Or.inr (hv.2.tsub_odd odd_one), ?_⟩
    rw [hcast]
    exact limit_large_exponent hv.1 hp ha

private theorem incompatible_denominators {a b c d : ℕ}
    (ha : Odd a) (hb : Even b) (hb0 : 0 < b) (hd : Odd d) :
    (a : ℝ) / b ≠ (c : ℝ) / d := by
  intro heq
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  have hnat : a * d = c * b := by
    exact_mod_cast (div_eq_div_iff hb' hd').mp heq
  apply (ha.mul hd).not_two_dvd_nat
  rw [hnat]
  exact (hb.mul_left c).two_dvd

private def Fiber (r : ℕ) (c : ℝ) : Set (Fin r → ℕ × ℕ) :=
  {x | (∀ i, Valid (x i)) ∧ (∏ i, localRatio (x i)) = c}

private theorem odd_denominator {r : ℕ} {x : Fin r → ℕ × ℕ} (hx : ∀ i, Valid (x i)) :
    ∃ a d : ℕ, Odd d ∧ (∏ i, localRatio (x i)) = (a : ℝ) / d := by
  let a (i : Fin r) : ℕ := σ 1 ((x i).1 ^ (x i).2)
  let d (i : Fin r) : ℕ := (x i).1 ^ (x i).2
  refine ⟨∏ i, a i, ∏ i, d i, ?_, ?_⟩
  · exact Finset.prod_induction d Odd (fun _ _ h₁ h₂ => h₁.mul h₂) odd_one
      (fun i _ => (hx i).2.1.pow)
  · simp only [Nat.cast_prod, ← Finset.prod_div_distrib, a, d, localRatio, abundance]

private theorem finite_fiber (r : ℕ) (c : ℝ) : (Fiber r c).Finite := by
  classical
  induction r generalizing c with
  | zero =>
    apply (Set.finite_singleton (fun _ : Fin 0 => ((0, 0) : ℕ × ℕ))).subset
    intro x _
    exact Set.mem_singleton_iff.mpr (funext fun i => Fin.elim0 i)
  | succ r ih =>
    by_contra hf
    let e := Set.Infinite.natEmbedding (Fiber (r + 1) c) hf
    let x : ℕ → Fin (r + 1) → ℕ × ℕ := fun m => (e m).1
    have hx : Function.Injective x := fun _ _ h => e.injective (Subtype.ext h)
    obtain ⟨φ, hφ, hclass⟩ := tuple_subsequence (r + 1) x
    let v : ℕ → Fin (r + 1) → ℕ × ℕ := fun m => x (φ m)
    have hvinj : Function.Injective v := hx.comp hφ.injective
    have hv (m : ℕ) : v m ∈ Fiber (r + 1) c := (e (φ m)).2
    have hvValid (m : ℕ) (i : Fin (r + 1)) : Valid (v m i) := (hv m).1 i
    have hvProd (m : ℕ) : (∏ i, localRatio (v m i)) = c := (hv m).2
    by_cases hfix : ∃ i y, ∀ m, v m i = y
    · obtain ⟨i, y, hy⟩ := hfix
      let w (m : ℕ) (j : Fin r) := v m (i.succAbove j)
      have hwinj : Function.Injective w := by
        intro l m hlm
        apply hvinj
        funext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
        · exact (hy l).trans (hy m).symm
        · exact congrFun hlm k
      have hyValid : Valid y := hy 0 ▸ hvValid 0 i
      have hy0 : localRatio y ≠ 0 :=
        (zero_lt_one.trans (one_lt_localRatio hyValid)).ne'
      have hw (m : ℕ) : w m ∈ Fiber r (c / localRatio y) := by
        refine ⟨fun j => hvValid m (i.succAbove j), ?_⟩
        have hprod := hvProd m
        rw [Fin.prod_univ_succAbove (fun j => localRatio (v m j)) i, hy m] at hprod
        apply (eq_div_iff hy0).2
        rw [mul_comm]
        exact hprod
      exact (Set.infinite_of_injective_forall_mem hwinj hw) (ih (c / localRatio y))
    · have hlim (i : Fin (r + 1)) :=
        coordinate_limit (fun m => hvValid m i) (hclass i)
          (fun ⟨y, hy⟩ => hfix ⟨i, y, hy⟩)
      choose b d hb hd hbd hlocal using hlim
      have hprodlim : Tendsto (fun m => ∏ i, localRatio (v m i)) atTop
          (𝓝 (∏ i, (b i : ℝ) / d i)) :=
        tendsto_finsetProd univ (fun i _ => hlocal i)
      have hc : c = ∏ i, (b i : ℝ) / d i :=
        tendsto_nhds_unique
          ((tendsto_const_nhds (x := c)).congr (fun m => (hvProd m).symm)) hprodlim
      have hc1 : 1 < c := by
        rw [← hvProd 0, ← Finset.prod_const_one (s := (univ : Finset (Fin (r + 1))))]
        exact Finset.prod_lt_prod_of_nonempty (fun _ _ => zero_lt_one)
          (fun i _ => one_lt_localRatio (hvValid 0 i)) ⟨0, mem_univ _⟩
      obtain ⟨i, hi⟩ : ∃ i, (b i : ℝ) / d i ≠ 1 := by
        by_contra! hall
        have hcEq : c = 1 := by rw [hc]; simp [hall]
        exact hc1.ne hcEq.symm
      have heven : Even (∏ j, d j) := by
        rw [Fin.prod_univ_succAbove d i]
        exact ((hbd i).resolve_left hi).mul_right _
      have hpos : 0 < ∏ j, d j :=
        CanonicallyOrderedAdd.prod_pos.mpr (fun j _ => hd j)
      have hodd : Odd (∏ j, b j) :=
        Finset.prod_induction b Odd (fun _ _ h₁ h₂ => h₁.mul h₂) odd_one
          (fun j _ => hb j)
      obtain ⟨a, z, hz, hrepr⟩ := odd_denominator (hvValid 0)
      apply incompatible_denominators (c := a) hodd heven hpos hz
      calc
        ((∏ j, b j : ℕ) : ℝ) / ((∏ j, d j : ℕ) : ℝ) =
            ∏ j, (b j : ℝ) / d j := by
              simp only [Nat.cast_prod, Finset.prod_div_distrib]
        _ = c := hc.symm
        _ = (a : ℝ) / z := (hvProd 0).symm.trans hrepr

private theorem finite_exact_width (r : ℕ) (c : ℝ) :
    {n : ℕ | Odd n ∧ abundance n = c ∧ n.primeFactors.card = r}.Finite := by
  classical
  let rebuild (x : Fin r → ℕ × ℕ) : ℕ := ∏ i, (x i).1 ^ (x i).2
  apply ((finite_fiber r c).image rebuild).subset
  intro n hn
  obtain ⟨hodd, hab, hcard⟩ := hn
  let e : Fin r ≃ n.primeFactors := (Finset.equivFinOfCardEq hcard).symm
  let x (i : Fin r) : ℕ × ℕ := ((e i).1, n.factorization (e i).1)
  have hvalid (i : Fin r) : Valid (x i) := by
    have hmem := (e i).2
    have hp := Nat.prime_of_mem_primeFactors hmem
    have hd := Nat.dvd_of_mem_primeFactors hmem
    have hpOdd : Odd (e i).1 :=
      hp.eq_two_or_odd'.resolve_left (fun he => hodd.not_two_dvd_nat (he ▸ hd))
    exact ⟨hp, hpOdd, hp.factorization_pos_of_dvd hodd.pos.ne' hd⟩
  refine ⟨x, ⟨hvalid, ?_⟩, ?_⟩
  · calc
      (∏ i, localRatio (x i)) =
          ∏ p : n.primeFactors, localRatio (p.1, n.factorization p.1) :=
        e.prod_comp (fun p => localRatio (p.1, n.factorization p.1))
      _ = ∏ p ∈ n.primeFactors, localRatio (p, n.factorization p) :=
        Finset.prod_coe_sort n.primeFactors (fun p => localRatio (p, n.factorization p))
      _ = abundance n := (abundance_factors hodd.pos.ne').symm
      _ = c := hab
  · calc
      rebuild x = ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization p :=
        e.prod_comp (fun p => (p : ℕ) ^ n.factorization p)
      _ = n := (Nat.prod_primeFactors_coe_pow_factorization hodd.pos.ne').symm

private theorem finite_bounded_width (r : ℕ) (c : ℝ) :
    {n : ℕ | Odd n ∧ abundance n = c ∧ n.primeFactors.card ≤ r}.Finite := by
  classical
  apply (Set.finite_iUnion (fun j : Fin (r + 1) => finite_exact_width j.val c)).subset
  intro n hn
  obtain ⟨hodd, hab, hcard⟩ := hn
  exact Set.mem_iUnion.2 ⟨⟨n.primeFactors.card, Nat.lt_succ_of_le hcard⟩,
    hodd, hab, rfl⟩

end OMA.Erdos1053FixedWidth

open OMA.Erdos1053FixedWidth in
theorem OMA.solution : OMA.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1.H1 := by
  intro r k _ _
  apply (finite_bounded_width r (k : ℝ)).subset
  intro n hn
  change ((Nat.IsPerfectFor n 1 k ∧ Odd n ∧ ¬ Squarefree n) ∧
    n.primeFactors.card ≤ r) at hn
  obtain ⟨⟨hperf, hodd, _⟩, hcard⟩ := hn
  change 0 < n ∧ σ 1 n = k * n at hperf
  refine ⟨hodd, ?_, hcard⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hperf.1.ne'
  exact (div_eq_iff hn0).2 (by exact_mod_cast hperf.2)
