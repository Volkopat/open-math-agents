import FormalConjectures.ErdosProblems.«417»

/-!
# Erdős 417(i) via least-preimage efficiencies

On each strip a*x < k ≤ b*x, the efficiency tests at b and a bound
the count of distinct totients attained by input x. After normalization
the limiting strip counts are the lower and upper sums of the threshold
frequencies. Their gap telescopes to at most one mesh width.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos417_erdos_417_parts_i_R1

open Nat Set Filter
open scoped Topology

/-- Regular variation of the number of distinct totients under fixed contractions. -/
def H1 : Prop :=
  let V (x : ℝ) := ({k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}.ncard : ℝ)
  ∀ t ∈ Ioc (0 : ℝ) 1, Tendsto (fun x ↦ V (t*x) / V x) atTop (𝓝 t)

/-- For each efficiency threshold t, the fraction of totients k admitting a
positive preimage m with k/m ≥ t has a limiting frequency. -/
def H2 : Prop :=
  let V (x : ℝ) := ({k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}.ncard : ℝ)
  let S (t x : ℝ) := {k : ℕ | (k : ℝ) ≤ x ∧
    ∃ m : ℕ, 1 ≤ m ∧ totient m = k ∧ t * m ≤ (k : ℝ)}
  ∀ t ∈ Icc (0 : ℝ) 1, ∃ p ∈ Icc (0 : ℝ) 1,
    Tendsto (fun x ↦ ((S t x).ncard : ℝ) / V x) atTop (𝓝 p)

lemma strip_count_le {A B C D : Set ℕ} (ha : A ⊆ B) (hc : C ⊆ D)
    (hb : B.Finite) (hd : D.Finite) (h : B \ A ⊆ D \ C) :
    (B.ncard : ℝ) - A.ncard ≤ (D.ncard : ℝ) - C.ncard := by
  have h₁ := ncard_sdiff_add_ncard_of_subset ha hb
  have h₂ := ncard_sdiff_add_ncard_of_subset hc hd
  have h₃ := ncard_le_ncard h (hd.sdiff (t := C))
  have hsum : (B.ncard : ℝ) + C.ncard ≤ D.ncard + A.ncard := by
    exact_mod_cast (show B.ncard + C.ncard ≤ D.ncard + A.ncard by omega)
  linarith

lemma squeeze_mesh {f : ℝ → ℝ} (h : ∀ n : ℕ, 0 < n →
    ∃ l u : ℝ, u-l ≤ 1/(n:ℝ) ∧ ∀ δ > 0, ∀ᶠ x in atTop,
      l-δ < f x ∧ f x < u+δ) : ∃ a, Tendsto f atTop (𝓝 a) := by
  suffices hc : Cauchy (map f atTop) from ⟨_, hc.le_nhds_lim⟩
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4/ε)
  have hn' : 0 < (n:ℝ) := lt_trans (by positivity : 0 < 4/ε) hn
  obtain ⟨l,u,hgap,he⟩ := h n (by exact_mod_cast hn')
  have hsmall : 1/(n:ℝ) < ε/2 := by
    apply (div_lt_iff₀ hn').2
    have := (div_lt_iff₀ hε).1 hn
    nlinarith
  refine ⟨Ioo (l-ε/4) (u+ε/4), he (ε/4) (by positivity), ?_⟩
  intro a ha b hb
  rw [Real.dist_eq, abs_lt]
  obtain ⟨ha₁,ha₂⟩ := ha
  obtain ⟨hb₁,hb₂⟩ := hb
  constructor <;> linarith

theorem main : H1 → H2 → type_of% @Erdos417.erdos_417.parts.i := by
  classical
  intro h₁ h₂
  let V (x : ℝ) := ({k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}.ncard : ℝ)
  let S (t x : ℝ) := {k : ℕ | (k : ℝ) ≤ x ∧
    ∃ m : ℕ, 1 ≤ m ∧ totient m = k ∧ t * m ≤ (k : ℝ)}
  let D (x : ℝ) := totient '' {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}
  let A (x z : ℝ) := {k : ℕ | (k : ℝ) ≤ z ∧ k ∈ D x}
  let f (x : ℝ) := ((D x).ncard : ℝ) / V x
  change ∀ t ∈ Ioc (0:ℝ) 1, Tendsto (fun x ↦ V (t*x) / V x) atTop (𝓝 t) at h₁
  change ∀ t ∈ Icc (0:ℝ) 1, ∃ p ∈ Icc (0:ℝ) 1,
    Tendsto (fun x ↦ ((S t x).ncard : ℝ) / V x) atTop (𝓝 p) at h₂
  have hV (x : ℝ) (hx : 0 ≤ x) : 0 < V x := by
    have hf : {k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}.Finite :=
      (finite_Iic ⌊x⌋₊).subset fun _ hk ↦ Nat.le_floor hk.2
    dsimp only [V]
    exact_mod_cast (ncard_pos hf).mpr ⟨totient 0, ⟨0,rfl⟩, by simpa using hx⟩
  have hzS (t : ℝ) : S t 0 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro k ⟨hk,m,hm,rfl,_⟩
    have hp := totient_pos.mpr (show 0 < m by omega)
    exact (not_lt_of_ge hk) (by exact_mod_cast hp)
  have hzA (x : ℝ) : A x 0 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro k ⟨hk,m,⟨hm,_⟩,rfl⟩
    have hp := totient_pos.mpr (show 0 < m by omega)
    exact (not_lt_of_ge hk) (by exact_mod_cast hp)
  have hAx (x : ℝ) : A x x = D x := by
    apply Subset.antisymm (fun _ h ↦ h.2)
    intro k hk
    refine ⟨?_,hk⟩
    obtain ⟨m,⟨_,hm⟩,rfl⟩ := hk
    exact (Nat.cast_le.mpr (totient_le m)).trans hm
  have hlim : ∃ a, Tendsto f atTop (𝓝 a) := by
    apply squeeze_mesh
    intro n hn
    let t (j : ℕ) := (j:ℝ) / n
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have ht (j : ℕ) (hj : j ≤ n) : t j ∈ Icc (0:ℝ) 1 :=
      ⟨by dsimp [t]; positivity, (div_le_one hn').mpr (by exact_mod_cast hj)⟩
    have hstep (j : ℕ) : t (j+1) - t j = 1/(n:ℝ) := by simp [t, add_div]
    have htpos (j : ℕ) : 0 < t (j+1) := by dsimp [t]; positivity
    let p (j : ℕ) := if hj : j ≤ n then (h₂ (t j) (ht j hj)).choose else 0
    have hp (j : ℕ) (hj : j ≤ n) :
        p j ∈ Icc (0:ℝ) 1 ∧
        Tendsto (fun x ↦ ((S (t j) x).ncard : ℝ) / V x) atTop (𝓝 (p j)) := by
      simpa [p,hj] using (h₂ (t j) (ht j hj)).choose_spec
    let C (i j : ℕ) (x : ℝ) := ((S (t i) (t j*x)).ncard : ℝ) / V x
    have hC (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
        Tendsto (C i j) atTop (𝓝 (p i * t j)) := by
      by_cases h : j = 0
      · subst j
        simpa [C,t,hzS] using (tendsto_const_nhds (x := (0:ℝ)) (f := (atTop : Filter ℝ)))
      have htj : 0 < t j := div_pos (by exact_mod_cast Nat.pos_of_ne_zero h) hn'
      have harg : Tendsto (fun x : ℝ ↦ t j*x) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos htj).mpr tendsto_id
      apply (((hp i hi).2.comp harg).mul (h₁ (t j) ⟨htj,(ht j hj).2⟩)).congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      dsimp [C, Function.comp_def]
      field_simp [(hV _ (mul_nonneg htj.le hx)).ne', (hV _ hx).ne']
    let B (d : ℕ) (x : ℝ) := ∑ j ∈ Finset.range n, (C (j+d) (j+1) x - C (j+d) j x)
    let b (d : ℕ) := ∑ j ∈ Finset.range n, p (j+d) / (n:ℝ)
    have hB (d : ℕ) (hd : d ≤ 1) : Tendsto (B d) atTop (𝓝 (b d)) := by
      apply tendsto_finsetSum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have heq : p (j+d) * t (j+1) - p (j+d) * t j = p (j+d) / n := by
        rw [← mul_sub,hstep]; ring
      rw [← heq]
      exact (hC _ _ (by omega) (by omega)).sub (hC _ _ (by omega) (by omega))
    have hgap : b 0 - b 1 ≤ 1/(n:ℝ) := by
      simp only [b, Nat.add_zero, ← Finset.sum_div]
      rw [← sub_div, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
      exact div_le_div_of_nonneg_right (by linarith [(hp 0 (by omega)).1.2, (hp n le_rfl).1.1]) hn'.le
    have hbounds (x : ℝ) (hx : 0 ≤ x) : B 1 x ≤ f x ∧ f x ≤ B 0 x := by
      let G (j : ℕ) := ((A x (t j*x)).ncard : ℝ) / V x
      have htotal : ∑ j ∈ Finset.range n, (G (j+1) - G j) = f x := by
        rw [Finset.sum_range_sub]
        simp [G,t,div_self hn'.ne',hzA,hAx,f]
      have hstrip (j : ℕ) :
          C (j+1) (j+1) x - C (j+1) j x ≤ G (j+1) - G j ∧
          G (j+1) - G j ≤ C j (j+1) x - C j j x := by
        let a := t j
        let b' := t (j+1)
        have ha : 0 ≤ a := by dsimp [a,t]; positivity
        have hb : 0 < b' := htpos j
        have hab : a*x ≤ b'*x := by
          apply mul_le_mul_of_nonneg_right _ hx
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hn'.le
        have fin {P : ℕ → Prop} {z : ℝ} : {k : ℕ | (k : ℝ) ≤ z ∧ P k}.Finite :=
          (finite_Iic ⌊z⌋₊).subset fun _ hk ↦ Nat.le_floor hk.1
        have monoS (u : ℝ) : S u (a*x) ⊆ S u (b'*x) := fun _ h ↦ ⟨h.1.trans hab,h.2⟩
        have monoA : A x (a*x) ⊆ A x (b'*x) := fun _ h ↦ ⟨h.1.trans hab,h.2⟩
        dsimp only [C,G]
        simp only [← sub_div]
        constructor <;> apply div_le_div_of_nonneg_right _ (hV x hx).le
        · apply strip_count_le (monoS b') monoA fin fin
          rintro k ⟨⟨hk,m,hm,he,hmk⟩,hlo⟩
          have hmx : (m:ℝ) ≤ x := le_of_mul_le_mul_left (hmk.trans hk) hb
          refine ⟨⟨hk,m,⟨hm,hmx⟩,he⟩,fun h ↦ hlo ⟨h.1,m,hm,he,hmk⟩⟩
        · apply strip_count_le monoA (monoS a) fin fin
          rintro k ⟨⟨hk,m,⟨hm,hmx⟩,he⟩,hlo⟩
          have hlow : ¬ (k:ℝ) ≤ a*x := fun h ↦ hlo ⟨h,m,⟨hm,hmx⟩,he⟩
          have hmk := (mul_le_mul_of_nonneg_left hmx ha).trans (lt_of_not_ge hlow).le
          exact ⟨⟨hk,m,hm,he,hmk⟩,fun h ↦ hlow h.1⟩
      rw [← htotal]
      exact ⟨Finset.sum_le_sum (fun j _ ↦ (hstrip j).1),
        Finset.sum_le_sum (fun j _ ↦ (hstrip j).2)⟩
    refine ⟨b 1,b 0,hgap,fun δ hδ ↦ ?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ),
      (tendsto_order.mp (hB 1 le_rfl)).1 (b 1-δ) (by linarith),
      (tendsto_order.mp (hB 0 (by omega))).2 (b 0+δ) (by linarith)] with x hx hl hu
    exact ⟨hl.trans_le (hbounds x hx).1, (hbounds x hx).2.trans_lt hu⟩
  obtain ⟨a,ha⟩ := hlim
  refine ⟨(ENNReal.ofReal a)⁻¹, ?_⟩
  apply (tendsto_inv_iff.2 (ENNReal.tendsto_ofReal ha)).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  dsimp only [f]
  rw [ENNReal.ofReal_div_of_pos (hV x hx)]
  rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl (ENNReal.ofReal_pos.mpr (hV x hx)).ne')]
  simp [V,D]

end OMA.R_Erdos417_erdos_417_parts_i_R1
