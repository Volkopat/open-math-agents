import OMAStatements.S_erdos_671

namespace OMA.P_erdos_671

open Filter Polynomial OMA.S_erdos_671
open scoped Topology Classical

/-! ### Part 1: Elementary Lagrange basis & product perturbation lemmas -/

private lemma lagrangeBasis_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    (lagrangeBasis a i).eval x = ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j) := by
  simp only [lagrangeBasis, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, inv_mul_eq_div]

private lemma lagrangeBasis_eval_self {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
    (i : Fin n) : (lagrangeBasis a i).eval (a i) = 1 := by
  rw [lagrangeBasis_eval]
  apply Finset.prod_eq_one
  intro j hj
  have hne : a i - a j ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) (ha h).symm)
  exact div_self hne

private lemma lagrangeBasis_eval_ne {n : ℕ} {a : Fin n → ℝ} {i k : Fin n} (hik : i ≠ k) :
    (lagrangeBasis a i).eval (a k) = 0 := by
  rw [lagrangeBasis_eval]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩)
  simp

private lemma lagrangeBasis_natDegree_le {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (lagrangeBasis a i).natDegree ≤ n - 1 := by
  unfold lagrangeBasis
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ j ∈ Finset.univ.erase i, (Polynomial.C (a i - a j)⁻¹ * (Polynomial.X - Polynomial.C (a j))).natDegree
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
        apply Finset.sum_le_sum; intro j _
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X]
    _ = n - 1 := by simp

private lemma lagrangeBasis_sum_eq_one {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (x : ℝ) :
    ∑ i : Fin n, (lagrangeBasis a i).eval x = 1 := by
  let P : Polynomial ℝ := (∑ i : Fin n, lagrangeBasis a i) - 1
  have hP0 : P = 0 := by
    by_contra hne
    have hdeg : P.natDegree ≤ n - 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ (by simp))
      exact le_trans (Polynomial.natDegree_sum_le _ _)
        (Finset.sup_le fun i _ => lagrangeBasis_natDegree_le a i)
    have hsub : (Finset.univ.image a).val ⊆ P.roots := by
      intro r hr
      rcases Finset.mem_image.mp (Finset.mem_def.mpr hr) with ⟨k, _, rfl⟩
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def]
      simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_one]
      rw [Finset.sum_eq_single k]
      · rw [lagrangeBasis_eval_self ha k, sub_self]
      · intro i _ hik; exact lagrangeBasis_eval_ne hik
      · intro hk; exact (hk (Finset.mem_univ k)).elim
    have hcard : n ≤ P.roots.card := by
      have h1 : (Finset.univ.image a).card = n := by
        rw [Finset.card_image_of_injective _ ha, Finset.card_fin]
      rw [← h1]
      exact Multiset.card_le_card (Multiset.le_iff_subset (Finset.univ.image a).nodup |>.mpr hsub)
    have hroots := Polynomial.card_roots' P
    omega
  have hev := congrArg (Polynomial.eval x) hP0
  simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_one,
    Polynomial.eval_zero, sub_eq_zero] at hev
  exact hev

private lemma lagrangeBasis_comp_equiv {n : ℕ} (a : Fin n → ℝ) (e : Fin n ≃ Fin n) (i : Fin n) :
    lagrangeBasis (a ∘ e) i = lagrangeBasis a (e i) := by
  unfold lagrangeBasis
  refine Finset.prod_equiv e ?_ ?_
  · intro j; simp [e.injective.eq_iff]
  · intro j _; rfl

private lemma lebesgueFun_comp_equiv {n : ℕ} (a : Fin n → ℝ) (e : Fin n ≃ Fin n) (x : ℝ) :
    lebesgueFun (a ∘ e) x = lebesgueFun a x := by
  unfold lebesgueFun
  simp_rw [lagrangeBasis_comp_equiv]
  exact Equiv.sum_comp e (fun j => |(lagrangeBasis a j).eval x|)

private lemma interpPoly_comp_equiv {n : ℕ} (a : Fin n → ℝ) (e : Fin n ≃ Fin n) (f : ℝ → ℝ) :
    interpPoly (a ∘ e) f = interpPoly a f := by
  unfold interpPoly
  simp_rw [lagrangeBasis_comp_equiv, Function.comp_apply]
  exact Equiv.sum_comp e (fun j => Polynomial.C (f (a j)) * lagrangeBasis a j)

private lemma prod_sub_prod_abs_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ)
    (C δ : ℝ) (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    (huv : ∀ i ∈ s, |u i| ≤ C ∧ |v i| ≤ C ∧ |u i - v i| ≤ δ) :
    |∏ i ∈ s, u i - ∏ i ∈ s, v i| ≤ (s.card : ℝ) * C ^ s.card * δ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.prod_insert hat, Finset.card_insert_of_notMem hat]
    have ha := huv a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, |u i| ≤ C ∧ |v i| ≤ C ∧ |u i - v i| ≤ δ :=
      fun i hi => huv i (Finset.mem_insert_of_mem hi)
    have hprod_v : |∏ i ∈ t, v i| ≤ C ^ t.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ t, |v i| ≤ ∏ _i ∈ t, C := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun i hi => (ht i hi).2.1)
        _ = C ^ t.card := Finset.prod_const C
    have hsplit : u a * ∏ i ∈ t, u i - v a * ∏ i ∈ t, v i =
        (u a - v a) * ∏ i ∈ t, v i + u a * (∏ i ∈ t, u i - ∏ i ∈ t, v i) := by ring
    rw [hsplit]
    have h1 := abs_add_le ((u a - v a) * ∏ i ∈ t, v i) (u a * (∏ i ∈ t, u i - ∏ i ∈ t, v i))
    rw [abs_mul, abs_mul] at h1
    have h2 : |u a - v a| * |∏ i ∈ t, v i| ≤ δ * C ^ t.card :=
      mul_le_mul ha.2.2 hprod_v (abs_nonneg _) hδ
    have h3 : |u a| * |∏ i ∈ t, u i - ∏ i ∈ t, v i| ≤ C * ((t.card : ℝ) * C ^ t.card * δ) :=
      mul_le_mul ha.1 (ih ht) (abs_nonneg _) (by linarith)
    have hCt : C ^ t.card ≤ C ^ (t.card + 1) := by
      rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hC
    push_cast
    calc |(u a - v a) * ∏ i ∈ t, v i + u a * (∏ i ∈ t, u i - ∏ i ∈ t, v i)|
      _ ≤ |u a - v a| * |∏ i ∈ t, v i| + |u a| * |∏ i ∈ t, u i - ∏ i ∈ t, v i| := h1
      _ ≤ δ * C ^ t.card + C * ((t.card : ℝ) * C ^ t.card * δ) := add_le_add h2 h3
      _ = C ^ t.card * δ + (t.card : ℝ) * C ^ (t.card + 1) * δ := by rw [pow_succ]; ring
      _ ≤ C ^ (t.card + 1) * δ + (t.card : ℝ) * C ^ (t.card + 1) * δ := by
          nlinarith [mul_le_mul_of_nonneg_right hCt hδ]
      _ = ((t.card : ℝ) + 1) * C ^ (t.card + 1) * δ := by ring

private lemma one_sub_div_pow_ge_half {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (m : ℝ))) ^ m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hge : (-2 : ℝ) ≤ -(1 / (2 * (m : ℝ))) := by
    have : 1 / (2 * (m : ℝ)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hbern := one_add_mul_le_pow hge m
  have heq : 1 + (m : ℝ) * -(1 / (2 * (m : ℝ))) = 1 / 2 := by field_simp; ring
  have hsub : 1 + -(1 / (2 * (m : ℝ))) = 1 - 1 / (2 * (m : ℝ)) := by ring
  rw [heq, hsub] at hbern
  exact hbern

private lemma one_add_div_pow_le_two {m : ℕ} (hm : 1 ≤ m) :
    (1 + 1 / (2 * (m : ℝ))) ^ m ≤ 2 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : 1 + 1 / (2 * (m : ℝ)) ≤ Real.exp (1 / (2 * (m : ℝ))) := by
    linarith [Real.add_one_le_exp (1 / (2 * (m : ℝ)))]
  have h2 : (1 + 1 / (2 * (m : ℝ))) ^ m ≤ Real.exp (1 / (2 * (m : ℝ))) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  rw [← Real.exp_nat_mul] at h2
  have heq : (m : ℝ) * (1 / (2 * (m : ℝ))) = 1 / 2 := by field_simp
  rw [heq] at h2
  have hexp_sq : Real.exp (1 / 2) ^ 2 ≤ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
    linarith [Real.exp_one_lt_d9]
  have hexp_le : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]
  exact le_trans h2 hexp_le

/-! ### Part 2: Explicit 1-indexed binary heap BFS-Cantor node array -/

/-- Target Lebesgue height at step `m`, depending only on tree depth `k = Nat.log 2 m`.
    Along every infinite branch `v_k` (`Nat.log 2 v_k = k`), this hits every positive integer i.o. -/
private def targetM (m : ℕ) : ℝ := (((Nat.log 2 m + 1).factorization 2 + 1 : ℕ) : ℝ)

private lemma targetM_ge_one (m : ℕ) : (1 : ℝ) ≤ targetM m := by
  unfold targetM; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)

private lemma exists_depth_targetM (M N : ℕ) :
    ∃ k ≥ N, (((k + 1).factorization 2 + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) := by
  refine ⟨2 ^ M * (2 * N + 1) - 1, ?_, ?_⟩
  · have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    have h2 : 2 * N + 1 ≤ 2 ^ M * (2 * N + 1) := Nat.le_mul_of_pos_left _ h1
    omega
  · have hpos : 1 ≤ 2 ^ M * (2 * N + 1) := Nat.mul_pos (Nat.two_pow_pos M) (by omega)
    have hadd : 2 ^ M * (2 * N + 1) - 1 + 1 = 2 ^ M * (2 * N + 1) := Nat.sub_add_cancel hpos
    rw [hadd, Nat.factorization_mul (Nat.two_pow_pos M).ne' (by omega)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    have h1 : (2 ^ M).factorization 2 = M := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]; simp
    have h2 : (2 * N + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by omega)
    rw [h1, h2, add_zero]

/-- Position `b j` of tree node `j` determined solely by step widths `s k` for `1 ≤ k ≤ j / 2`. -/
private def nodePos (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | j + 2 =>
    let p := (j + 2) / 2
    if (j + 2) % 2 = 0 then nodePos s p else nodePos s p + s p

private lemma nodePos_two_mul (s : ℕ → ℝ) {v : ℕ} (hv : 1 ≤ v) :
    nodePos s (2 * v) = nodePos s v := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  have h : 2 * (u + 1) = 2 * u + 2 := by omega
  rw [h, nodePos]
  simp only [show (2 * u + 2) % 2 = 0 by omega, ↓reduceIte,
    show (2 * u + 2) / 2 = u + 1 by omega]

private lemma nodePos_two_mul_add_one (s : ℕ → ℝ) {v : ℕ} (hv : 1 ≤ v) :
    nodePos s (2 * v + 1) = nodePos s v + s v := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  have h : 2 * (u + 1) + 1 = (2 * u + 1) + 2 := by omega
  rw [h, nodePos]
  have hmod : ((2 * u + 1) + 2) % 2 ≠ 0 := by omega
  have hdiv : ((2 * u + 1) + 2) / 2 = u + 1 := by omega
  simp only [hmod, ↓reduceIte, hdiv]

private lemma nodePos_congr {s1 s2 : ℕ → ℝ} {m : ℕ} (h : ∀ k < m, s1 k = s2 k) :
    ∀ j < 2 * m, nodePos s1 j = nodePos s2 j := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    match j with
    | 0 => simp [nodePos]
    | 1 => simp [nodePos]
    | k + 2 =>
      simp only [nodePos]
      have hp_lt_j : (k + 2) / 2 < k + 2 := by omega
      have hp_lt_m : (k + 2) / 2 < m := by omega
      have hp_lt_2m : (k + 2) / 2 < 2 * m := by omega
      rw [ih _ hp_lt_j hp_lt_2m, h _ hp_lt_m]

private structure TreeState where
  s : ℕ → ℝ
  δ : ℕ → ℝ
  ρ : ℕ → ℝ

private noncomputable def stepState (m : ℕ) (st : TreeState) : TreeState :=
  if m = 0 then st else
  let g : ℝ := if m = 1 then 1 / 4 else st.s (m - 1)
  let b : ℕ → ℝ := nodePos st.s
  let D : ℝ := (∏ j ∈ (Finset.Ico m (2 * m)).erase m, |b m - b j|) /
    (∏ j ∈ Finset.Ico m (2 * m), (1 + b j))
  let s_prev : ℝ := if m = 1 then 1 else st.ρ (m - 1) / 4
  let s_gap : ℝ := g / (16 * (m : ℝ))
  let s_del : ℝ := 1 / (2 ^ m * (16 * (m : ℝ) * D + 1))
  let s_err : ℝ := 1 / (4 * 2 ^ m * (6 * (m : ℝ) * (2 / g) ^ m + 4 * (m : ℝ) * 6 ^ m + 1))
  let sm : ℝ := min (1 / 8) (min s_prev (min s_gap (min s_del s_err)))
  let δm : ℝ := D * sm / targetM m
  let ρ_prev : ℝ := if m = 1 then 1 else st.ρ (m - 1)
  let ρm : ℝ := min ρ_prev (min (sm / 8) (δm / (4 * 6 ^ m)))
  { s := Function.update st.s m sm
    δ := Function.update st.δ m δm
    ρ := Function.update st.ρ m ρm }

private noncomputable def treeState : ℕ → TreeState
  | 0 => { s := fun _ => 1, δ := fun _ => 1, ρ := fun _ => 1 }
  | m + 1 => stepState m (treeState m)

private noncomputable def sSeq (m : ℕ) : ℝ := (treeState (m + 1)).s m
private noncomputable def δSeq (m : ℕ) : ℝ := (treeState (m + 1)).δ m
private noncomputable def ρSeq (m : ℕ) : ℝ := (treeState (m + 1)).ρ m
private noncomputable def bPos (j : ℕ) : ℝ := nodePos sSeq j

private lemma treeState_s_stable {k n : ℕ} (hk : k < n) :
    (treeState n).s k = sSeq k := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hkm : k = m
    · subst hkm; rfl
    · have hklt : k < m := by omega
      by_cases hm0 : m = 0
      · omega
      · simp only [treeState, stepState, hm0, ↓reduceIte]
        rw [Function.update_of_ne (by omega)]; exact ih hklt

private lemma treeState_δ_stable {k n : ℕ} (hk : k < n) :
    (treeState n).δ k = δSeq k := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hkm : k = m
    · subst hkm; rfl
    · have hklt : k < m := by omega
      by_cases hm0 : m = 0
      · omega
      · simp only [treeState, stepState, hm0, ↓reduceIte]
        rw [Function.update_of_ne (by omega)]; exact ih hklt

private lemma treeState_ρ_stable {k n : ℕ} (hk : k < n) :
    (treeState n).ρ k = ρSeq k := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hkm : k = m
    · subst hkm; rfl
    · have hklt : k < m := by omega
      by_cases hm0 : m = 0
      · omega
      · simp only [treeState, stepState, hm0, ↓reduceIte]
        rw [Function.update_of_ne (by omega)]; exact ih hklt

private lemma nodePos_treeState_eq {m j : ℕ} (hj : j < 2 * m) :
    nodePos (treeState m).s j = bPos j :=
  nodePos_congr (fun _ hk => treeState_s_stable hk) j hj

private noncomputable def gSeq (m : ℕ) : ℝ := if m = 1 then 1 / 4 else sSeq (m - 1)

private noncomputable def DSeq (m : ℕ) : ℝ :=
  (∏ j ∈ (Finset.Ico m (2 * m)).erase m, |bPos m - bPos j|) /
    (∏ j ∈ Finset.Ico m (2 * m), (1 + bPos j))

private lemma sSeq_eq {m : ℕ} (hm : 1 ≤ m) :
    sSeq m = min (1 / 8) (min (if m = 1 then 1 else ρSeq (m - 1) / 4)
      (min (gSeq m / (16 * (m : ℝ)))
        (min (1 / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)))
          (1 / (4 * 2 ^ m * (6 * (m : ℝ) * (2 / gSeq m) ^ m + 4 * (m : ℝ) * 6 ^ m + 1)))))) := by
  unfold sSeq
  simp only [treeState, stepState, show m ≠ 0 by omega, ↓reduceIte, Function.update_self]
  have hg : (if m = 1 then (1 : ℝ) / 4 else (treeState m).s (m - 1)) = gSeq m := by
    unfold gSeq
    split_ifs with h1
    · rfl
    · exact treeState_s_stable (by omega)
  have hρ : (if m = 1 then (1 : ℝ) else (treeState m).ρ (m - 1) / 4) =
      (if m = 1 then 1 else ρSeq (m - 1) / 4) := by
    split_ifs with h1
    · rfl
    · rw [treeState_ρ_stable (by omega)]
  have hD : (∏ j ∈ (Finset.Ico m (2 * m)).erase m, |nodePos (treeState m).s m - nodePos (treeState m).s j|) /
      (∏ j ∈ Finset.Ico m (2 * m), (1 + nodePos (treeState m).s j)) = DSeq m := by
    unfold DSeq; congr 1
    · apply Finset.prod_congr rfl; intro j hj
      rw [nodePos_treeState_eq (by omega), nodePos_treeState_eq (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hj)).2]
    · apply Finset.prod_congr rfl; intro j hj
      rw [nodePos_treeState_eq (Finset.mem_Ico.mp hj).2]
  rw [hg, hρ, hD]

private lemma δSeq_eq {m : ℕ} (hm : 1 ≤ m) : δSeq m = DSeq m * sSeq m / targetM m := by
  unfold δSeq
  simp only [treeState, stepState, show m ≠ 0 by omega, ↓reduceIte, Function.update_self]
  have hD : (∏ j ∈ (Finset.Ico m (2 * m)).erase m, |nodePos (treeState m).s m - nodePos (treeState m).s j|) /
      (∏ j ∈ Finset.Ico m (2 * m), (1 + nodePos (treeState m).s j)) = DSeq m := by
    unfold DSeq; congr 1
    · apply Finset.prod_congr rfl; intro j hj
      rw [nodePos_treeState_eq (by omega), nodePos_treeState_eq (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hj)).2]
    · apply Finset.prod_congr rfl; intro j hj
      rw [nodePos_treeState_eq (Finset.mem_Ico.mp hj).2]
  have hs : min (1 / 8) (min (if m = 1 then 1 else (treeState m).ρ (m - 1) / 4)
      (min ((if m = 1 then (1 : ℝ) / 4 else (treeState m).s (m - 1)) / (16 * (m : ℝ)))
        (min (1 / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)))
          (1 / (4 * 2 ^ m * (6 * (m : ℝ) * (2 / (if m = 1 then (1 : ℝ) / 4 else (treeState m).s (m - 1))) ^ m +
            4 * (m : ℝ) * 6 ^ m + 1)))))) = sSeq m := by
    rw [sSeq_eq hm]
    have hg : (if m = 1 then (1 : ℝ) / 4 else (treeState m).s (m - 1)) = gSeq m := by
      unfold gSeq
      split_ifs with h1
      · rfl
      · exact treeState_s_stable (by omega)
    have hρ : (if m = 1 then (1 : ℝ) else (treeState m).ρ (m - 1) / 4) =
        (if m = 1 then 1 else ρSeq (m - 1) / 4) := by
      split_ifs with h1
      · rfl
      · rw [treeState_ρ_stable (by omega)]
    rw [hg, hρ]
  rw [hD, hs]

private lemma ρSeq_eq {m : ℕ} (hm : 1 ≤ m) :
    ρSeq m = min (if m = 1 then 1 else ρSeq (m - 1)) (min (sSeq m / 8) (δSeq m / (4 * 6 ^ m))) := by
  have h1 : ρSeq m = min (if m = 1 then 1 else (treeState m).ρ (m - 1))
      (min (sSeq m / 8) (δSeq m / (4 * 6 ^ m))) := by
    unfold ρSeq
    simp only [treeState, stepState, show m ≠ 0 by omega, ↓reduceIte, Function.update_self]
    have hs_eq : sSeq m = (treeState (m + 1)).s m := rfl
    have hδ_eq : δSeq m = (treeState (m + 1)).δ m := rfl
    rw [hs_eq, hδ_eq]
    simp only [treeState, stepState, show m ≠ 0 by omega, ↓reduceIte, Function.update_self]
  rw [h1]
  split_ifs with h2
  · rfl
  · rw [treeState_ρ_stable (by omega)]

/-! ### Part 3: Inductive positivity, separation, and bounds for the heap tree -/

private lemma bPos_nonneg_and_le_sum (hpos : ∀ k, 1 ≤ k → 0 < sSeq k) :
    ∀ j : ℕ, 0 ≤ bPos j ∧ bPos j ≤ ∑ k ∈ Finset.Ico 1 j, sSeq k := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    match j with
    | 0 => simp [bPos, nodePos]
    | 1 => simp [bPos, nodePos]
    | u + 2 =>
      set p := (u + 2) / 2
      have hp_pos : 1 ≤ p := by omega
      have hp_lt : p < u + 2 := by omega
      obtain ⟨hnn, hle⟩ := ih p hp_lt
      have hsub : Finset.Ico 1 p ⊆ (Finset.Ico 1 (u + 2)).erase p := by
        intro x hx; simp only [Finset.mem_erase, Finset.mem_Ico] at hx ⊢; omega
      have hmem : p ∈ Finset.Ico 1 (u + 2) := Finset.mem_Ico.mpr ⟨hp_pos, hp_lt⟩
      have hsum_step : ∑ k ∈ Finset.Ico 1 p, sSeq k + sSeq p ≤ ∑ k ∈ Finset.Ico 1 (u + 2), sSeq k := by
        rw [← Finset.add_sum_erase _ _ hmem, add_comm]
        exact add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ =>
          (hpos k (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hk)).1).le)) _
      have hsp_nn : 0 ≤ sSeq p := (hpos p hp_pos).le
      unfold bPos at hnn hle ⊢; simp only [nodePos]
      split_ifs
      · exact ⟨hnn, by linarith⟩
      · exact ⟨by linarith, by linarith⟩

private lemma tree_inv :
    ∀ m : ℕ, 1 ≤ m →
      (∀ k, 1 ≤ k → k < m → 0 < sSeq k ∧ 0 < δSeq k ∧ 0 < ρSeq k) ∧
      (∀ k, 1 ≤ k → k < m → sSeq k ≤ 1 / 8) ∧
      (∀ k, 2 ≤ k → k < m → sSeq k ≤ sSeq (k - 1) / 32) ∧
      (∀ j ∈ Finset.Ico m (2 * m), 0 ≤ bPos j) ∧
      (∀ i ∈ Finset.Ico m (2 * m), ∀ j ∈ Finset.Ico m (2 * m), i ≠ j → gSeq m ≤ |bPos i - bPos j|) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨fun k _ h => by omega, fun k _ h => by omega, fun k _ h => by omega, ?_, ?_⟩
    · intro j hj; have : j = 1 := by simp only [Finset.mem_Ico] at hj; omega
      subst this; simp [bPos, nodePos]
    · intro i hi j hj hij
      simp only [Finset.mem_Ico] at hi hj; omega
  | succ m hm ih =>
    obtain ⟨hpos_prev, hle18_prev, hdec_prev, hbnn_prev, hsep_prev⟩ := ih
    have hg_pos : 0 < gSeq m := by
      unfold gSeq; split_ifs with h1
      · norm_num
      · exact (hpos_prev (m - 1) (by omega) (by omega)).1
    have hD_pos : 0 < DSeq m := by
      unfold DSeq
      apply div_pos
      · apply Finset.prod_pos; intro j hj
        have hj' := Finset.mem_erase.mp hj
        have hm_mem : m ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
        exact lt_of_lt_of_le hg_pos (hsep_prev m hm_mem j hj'.2 hj'.1.symm)
      · apply Finset.prod_pos; intro j hj
        have := hbnn_prev j hj; linarith
    have hs_pos : 0 < sSeq m := by
      rw [sSeq_eq hm]
      have hρp : 0 < (if m = 1 then (1 : ℝ) else ρSeq (m - 1) / 4) := by
        split_ifs with h1; · norm_num
        · exact div_pos (hpos_prev (m - 1) (by omega) (by omega)).2.2 (by norm_num)
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have hδ_pos : 0 < δSeq m := by
      rw [δSeq_eq hm]
      have hM := targetM_ge_one m
      exact div_pos (mul_pos hD_pos hs_pos) (by linarith)
    have hρ_pos : 0 < ρSeq m := by
      rw [ρSeq_eq hm]
      have hρp : 0 < (if m = 1 then (1 : ℝ) else ρSeq (m - 1)) := by
        split_ifs with h1; · norm_num
        · exact (hpos_prev (m - 1) (by omega) (by omega)).2.2
      positivity
    have hs_le18 : sSeq m ≤ 1 / 8 := by rw [sSeq_eq hm]; exact min_le_left _ _
    have hs_le_gap : sSeq m ≤ gSeq m / (16 * (m : ℝ)) := by
      rw [sSeq_eq hm]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_le_g8 : sSeq m ≤ gSeq m / 8 := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have : gSeq m / (16 * (m : ℝ)) ≤ gSeq m / 8 := by
        apply div_le_div_of_nonneg_left hg_pos.le (by norm_num) (by linarith)
      linarith
    have hdec_m : 2 ≤ m → sSeq m ≤ sSeq (m - 1) / 32 := by
      intro hm2
      have h1 : sSeq m ≤ ρSeq (m - 1) / 4 := by
        have h : sSeq m ≤ (if m = 1 then (1 : ℝ) else ρSeq (m - 1) / 4) := by
          rw [sSeq_eq hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
        simp only [show m ≠ 1 by omega, ↓reduceIte] at h
        exact h
      have h2 : ρSeq (m - 1) ≤ sSeq (m - 1) / 8 := by
        rw [ρSeq_eq (by omega)]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk1 hklt
      by_cases hkm : k = m
      · subst hkm; exact ⟨hs_pos, hδ_pos, hρ_pos⟩
      · exact hpos_prev k hk1 (by omega)
    · intro k hk1 hklt
      by_cases hkm : k = m
      · subst hkm; exact hs_le18
      · exact hle18_prev k hk1 (by omega)
    · intro k hk2 hklt
      by_cases hkm : k = m
      · subst hkm; exact hdec_m hk2
      · exact hdec_prev k hk2 (by omega)
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      by_cases hj1 : j < 2 * m
      · exact hbnn_prev j (Finset.mem_Ico.mpr ⟨by omega, hj1⟩)
      · by_cases hj2 : j = 2 * m
        · subst hj2
          have h2m : bPos (2 * m) = bPos m := nodePos_two_mul sSeq hm
          rw [h2m]; exact hbnn_prev m (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
        · have hj3 : j = 2 * m + 1 := by omega
          subst hj3
          have h2m1 : bPos (2 * m + 1) = bPos m + sSeq m := nodePos_two_mul_add_one sSeq hm
          rw [h2m1]
          have := hbnn_prev m (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
          linarith
    · intro i hi j hj hij
      have hg_succ : gSeq (m + 1) = sSeq m := by unfold gSeq; rw [if_neg (by omega)]; simp
      rw [hg_succ]
      simp only [Finset.mem_Ico] at hi hj
      have hm_mem : m ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
      have h2m : bPos (2 * m) = bPos m := nodePos_two_mul sSeq hm
      have h2m1 : bPos (2 * m + 1) = bPos m + sSeq m := nodePos_two_mul_add_one sSeq hm
      by_cases hi2m : i < 2 * m <;> by_cases hj2m : j < 2 * m
      · have h := hsep_prev i (Finset.mem_Ico.mpr ⟨by omega, hi2m⟩) j (Finset.mem_Ico.mpr ⟨by omega, hj2m⟩) hij
        linarith
      · have h_old := hsep_prev i (Finset.mem_Ico.mpr ⟨by omega, hi2m⟩) m hm_mem (by omega)
        by_cases hj_eq : j = 2 * m
        · subst hj_eq; rw [h2m]; linarith
        · have hj_eq1 : j = 2 * m + 1 := by omega
          subst hj_eq1; rw [h2m1]
          have htri : |bPos i - bPos m| ≤ |bPos i - (bPos m + sSeq m)| + sSeq m := by
            have := abs_add_le (bPos i - (bPos m + sSeq m)) (sSeq m)
            rw [abs_of_pos hs_pos] at this
            have heq : bPos i - (bPos m + sSeq m) + sSeq m = bPos i - bPos m := by ring
            rw [heq] at this; exact this
          linarith
      · have h_old := hsep_prev m hm_mem j (Finset.mem_Ico.mpr ⟨by omega, hj2m⟩) (by omega)
        by_cases hi_eq : i = 2 * m
        · subst hi_eq; rw [h2m]; linarith
        · have hi_eq1 : i = 2 * m + 1 := by omega
          subst hi_eq1; rw [h2m1]
          have htri : |bPos m - bPos j| ≤ |bPos m + sSeq m - bPos j| + sSeq m := by
            have := abs_add_le (bPos m + sSeq m - bPos j) (-sSeq m)
            rw [abs_neg, abs_of_pos hs_pos] at this
            have heq : bPos m + sSeq m - bPos j + -sSeq m = bPos m - bPos j := by ring
            rw [heq] at this; exact this
          linarith
      · by_cases hi_eq : i = 2 * m
        · have hj_eq1 : j = 2 * m + 1 := by omega
          subst hi_eq hj_eq1; rw [h2m, h2m1]
          have : bPos m - (bPos m + sSeq m) = -sSeq m := by ring
          rw [this, abs_neg, abs_of_pos hs_pos]
        · have hi_eq1 : i = 2 * m + 1 := by omega
          have hj_eq : j = 2 * m := by omega
          subst hi_eq1 hj_eq; rw [h2m, h2m1]
          have : bPos m + sSeq m - bPos m = sSeq m := by ring
          rw [this, abs_of_pos hs_pos]

private lemma sSeq_pos {m : ℕ} (hm : 1 ≤ m) : 0 < sSeq m :=
  ((tree_inv (m + 1) (by omega)).1 m hm (by omega)).1

private lemma δSeq_pos {m : ℕ} (hm : 1 ≤ m) : 0 < δSeq m :=
  ((tree_inv (m + 1) (by omega)).1 m hm (by omega)).2.1

private lemma ρSeq_pos {m : ℕ} (hm : 1 ≤ m) : 0 < ρSeq m :=
  ((tree_inv (m + 1) (by omega)).1 m hm (by omega)).2.2

private lemma gSeq_pos {m : ℕ} (hm : 1 ≤ m) : 0 < gSeq m := by
  unfold gSeq
  split_ifs with h1
  · norm_num
  · exact sSeq_pos (by omega)

private lemma sSeq_le_div32 {m : ℕ} (hm : 1 ≤ m) : sSeq (m + 1) ≤ sSeq m / 32 := by
  have h := (tree_inv (m + 2) (by omega)).2.2.1 (m + 1) (by omega) (by omega)
  simpa using h

private lemma ρSeq_anti {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : ρSeq b ≤ ρSeq a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k hak ih =>
    have hstep : ρSeq (k + 1) ≤ ρSeq k := by
      have h : ρSeq (k + 1) ≤ (if k + 1 = 1 then (1 : ℝ) else ρSeq (k + 1 - 1)) := by
        rw [ρSeq_eq (by omega)]; exact min_le_left _ _
      simpa [show k ≠ 0 by omega] using h
    exact le_trans hstep ih

private lemma sSeq_le_ρSeq_div4 {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    sSeq b ≤ ρSeq a / 4 := by
  have h1 : sSeq b ≤ ρSeq (b - 1) / 4 := by
    have h : sSeq b ≤ (if b = 1 then (1 : ℝ) else ρSeq (b - 1) / 4) := by
      rw [sSeq_eq (by omega)]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    simpa [show b ≠ 1 by omega] using h
  have h2 : ρSeq (b - 1) ≤ ρSeq a := ρSeq_anti ha (by omega)
  linarith

private lemma sSeq_tail_sum {m N : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m (m + N), sSeq k ≤ 2 * sSeq m := by
  have hbound : ∀ t : ℕ, sSeq (m + t) ≤ sSeq m * ((1 : ℝ) / 2) ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep : sSeq (m + t + 1) ≤ sSeq (m + t) / 32 := sSeq_le_div32 (by omega)
      have hpos := (sSeq_pos (by omega : 1 ≤ m + t)).le
      calc sSeq (m + (t + 1)) = sSeq (m + t + 1) := by ring_nf
        _ ≤ sSeq (m + t) / 32 := hstep
        _ ≤ sSeq (m + t) * (1 / 2) := by linarith
        _ ≤ (sSeq m * ((1 : ℝ) / 2) ^ t) * (1 / 2) := mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = sSeq m * ((1 : ℝ) / 2) ^ (t + 1) := by rw [pow_succ]; ring
  have hre : ∑ k ∈ Finset.Ico m (m + N), sSeq k = ∑ t ∈ Finset.range N, sSeq (m + t) := by
    apply Finset.sum_bij (fun k _ => k - m)
    · intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro a ha b hb h; simp only [Finset.mem_Ico] at ha hb; omega
    · intro t ht; refine ⟨m + t, Finset.mem_Ico.mpr ⟨by omega, by rw [Finset.mem_range] at ht; omega⟩, by omega⟩
    · intro k hk; simp only [Finset.mem_Ico] at hk; congr 1; omega
  rw [hre]
  calc ∑ t ∈ Finset.range N, sSeq (m + t)
    _ ≤ ∑ t ∈ Finset.range N, sSeq m * ((1 : ℝ) / 2) ^ t := Finset.sum_le_sum fun t _ => hbound t
    _ = sSeq m * ∑ t ∈ Finset.range N, ((1 : ℝ) / 2) ^ t := (Finset.mul_sum _ _ _).symm
    _ ≤ sSeq m * 2 := by
        apply mul_le_mul_of_nonneg_left _ (sSeq_pos hm).le
        rw [geom_sum_eq (by norm_num : (1 : ℝ) / 2 ≠ 1)]
        have hrew : (((1 : ℝ) / 2) ^ N - 1) / ((1 : ℝ) / 2 - 1) = 2 - 2 * ((1 : ℝ) / 2) ^ N := by ring
        have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ N := by positivity
        linarith
    _ = 2 * sSeq m := mul_comm _ _

private lemma bPos_mem_Icc (j : ℕ) : bPos j ∈ Set.Icc (0 : ℝ) (1 / 4) := by
  obtain ⟨hnn, hle⟩ := bPos_nonneg_and_le_sum (fun k hk => sSeq_pos hk) j
  refine ⟨hnn, ?_⟩
  by_cases hj : j ≤ 1
  · have : Finset.Ico 1 j = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty] at hle; linarith
  · have h1 : Finset.Ico 1 j = Finset.Ico 1 (1 + (j - 1)) := by congr 1; omega
    rw [h1] at hle
    have h2 := sSeq_tail_sum (m := 1) (N := j - 1) le_rfl
    have h3 : sSeq 1 ≤ 1 / 8 := (tree_inv 2 (by omega)).2.1 1 le_rfl (by omega)
    linarith

private lemma DSeq_pos {m : ℕ} (hm : 1 ≤ m) : 0 < DSeq m := by
  unfold DSeq
  apply div_pos
  · apply Finset.prod_pos; intro j hj
    have hj' := Finset.mem_erase.mp hj
    have hm_mem : m ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    exact lt_of_lt_of_le (gSeq_pos hm) ((tree_inv m hm).2.2.2.2 m hm_mem j hj'.2 hj'.1.symm)
  · apply Finset.prod_pos; intro j _
    have := (bPos_mem_Icc j).1; linarith

private lemma δSeq_bounds {m : ℕ} (hm : 1 ≤ m) :
    δSeq m ≤ 1 / (16 * (m : ℝ)) ∧ δSeq m ≤ 1 / 2 ^ m := by
  have hs_del : sSeq m ≤ 1 / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)) := by
    rw [sSeq_eq hm]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hD := DSeq_pos hm
  have hM := targetM_ge_one m
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hδ_le : δSeq m ≤ DSeq m * sSeq m := by
    rw [δSeq_eq hm]; exact div_le_self (mul_nonneg hD.le (sSeq_pos hm).le) hM
  have hDs : DSeq m * sSeq m ≤ DSeq m / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)) := by
    rw [div_eq_mul_inv]
    simpa [one_div] using mul_le_mul_of_nonneg_left hs_del hD.le
  constructor
  · have h1 : DSeq m / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)) ≤ 1 / (16 * (m : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hnn : 0 ≤ 16 * (m : ℝ) * DSeq m + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_right h2m hnn
      linarith
    linarith
  · have h1 : DSeq m / (2 ^ m * (16 * (m : ℝ) * DSeq m + 1)) ≤ 1 / 2 ^ m := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h16 : DSeq m ≤ 16 * (m : ℝ) * DSeq m + 1 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left h16 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)
      linarith
    linarith

/-! ### Part 4: Constructing the sorted node matrix `aNodes` and transferring bounds -/

private noncomputable def rawNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  if i.val = 0 then -1
  else if i.val = 1 then -1 + δSeq m
  else bPos (m + (i.val - 2))

private lemma rawNode_mem_Icc {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 2)) :
    rawNode m i ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold rawNode
  split_ifs with h0 h1
  · constructor <;> norm_num
  · have hpos := δSeq_pos hm
    have hle := (δSeq_bounds hm).1
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : δSeq m ≤ 1 / 4 := le_trans hle (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    constructor <;> linarith
  · have hb := bPos_mem_Icc (m + (i.val - 2))
    constructor <;> linarith [hb.1, hb.2]

private lemma rawNode_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective (rawNode m) := by
  have hpos := δSeq_pos hm
  have hle := (δSeq_bounds hm).1
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hδ4 : δSeq m ≤ 1 / 4 := le_trans hle (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  intro i j hij
  ext
  unfold rawNode at hij
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
  · omega
  · by_cases hj1 : j.val = 1
    · simp only [hi0, hj1, Nat.one_ne_zero, ↓reduceIte] at hij; linarith
    · simp only [hi0, hj0, hj1, ↓reduceIte] at hij
      have := (bPos_mem_Icc (m + (j.val - 2))).1; linarith
  · by_cases hi1 : i.val = 1
    · simp only [hi1, hj0, Nat.one_ne_zero, ↓reduceIte] at hij; linarith
    · simp only [hi0, hi1, hj0, ↓reduceIte] at hij
      have := (bPos_mem_Icc (m + (i.val - 2))).1; linarith
  · by_cases hi1 : i.val = 1 <;> by_cases hj1 : j.val = 1
    · omega
    · simp only [hi1, hj0, hj1, Nat.one_ne_zero, ↓reduceIte] at hij
      have := (bPos_mem_Icc (m + (j.val - 2))).1; linarith
    · simp only [hi0, hi1, hj1, Nat.one_ne_zero, ↓reduceIte] at hij
      have := (bPos_mem_Icc (m + (i.val - 2))).1; linarith
    · simp only [hi0, hi1, hj0, hj1, ↓reduceIte] at hij
      have hi_mem : m + (i.val - 2) ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hj_mem : m + (j.val - 2) ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      by_contra hne
      have hsep := (tree_inv m hm).2.2.2.2 _ hi_mem _ hj_mem (by omega)
      rw [hij, sub_self, abs_zero] at hsep
      linarith [gSeq_pos hm]

private lemma rawNode_image_card {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ.image (rawNode m)).card = m + 2 := by
  rw [Finset.card_image_of_injective Finset.univ (rawNode_injective hm), Finset.card_fin]

private noncomputable def aNodesRaw (m : ℕ) (hm : 1 ≤ m) : Fin (m + 2) → ℝ :=
  fun i => ((Finset.univ.image (rawNode m)).orderEmbOfFin (rawNode_image_card hm)) i

private noncomputable def aNodes : (n : ℕ) → Fin n → ℝ
  | 0 => fun i => i.elim0
  | 1 => fun _ => 0
  | 2 => fun i => -1 + (i.val : ℝ) / 3
  | m + 3 => aNodesRaw (m + 1) (Nat.succ_pos m)

private lemma aNodes_valid (n : ℕ) (_hn : 1 ≤ n) :
    StrictMono (aNodes n) ∧ ∀ i : Fin n, aNodes n i ∈ Set.Icc (-1 : ℝ) 1 := by
  match n with
  | 0 => omega
  | 1 =>
    refine ⟨fun i j hij => by omega, fun _ => by simp only [aNodes]; constructor <;> norm_num⟩
  | 2 =>
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [aNodes, add_lt_add_iff_left]
      exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (by norm_num)
    · simp only [aNodes]
      have hi : (i.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (by omega : i.val < 3)
      have hnn : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
      constructor <;> linarith
  | m + 3 =>
    refine ⟨(Finset.orderEmbOfFin _ (rawNode_image_card (Nat.succ_pos m))).strictMono, fun i => ?_⟩
    have hmem := Finset.orderEmbOfFin_mem (Finset.univ.image (rawNode (m + 1))) (rawNode_image_card (Nat.succ_pos m)) i
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    simp only [aNodes, aNodesRaw]
    rw [← hj]; exact rawNode_mem_Icc (Nat.succ_pos m) j

private lemma aNodes_equiv_rawNode {m : ℕ} (hm : 1 ≤ m) :
    ∃ e : Fin (m + 2) ≃ Fin (m + 2), aNodes (m + 2) ∘ e = rawNode m := by
  obtain ⟨u, rfl⟩ : ∃ u, m = u + 1 := ⟨m - 1, by omega⟩
  have h1 : 1 ≤ u + 1 := Nat.succ_pos u
  set S := Finset.univ.image (rawNode (u + 1))
  have hcard : S.card = u + 1 + 2 := rawNode_image_card h1
  have hinj := rawNode_injective h1
  have hsurj : Function.Surjective (fun i : Fin (u + 1 + 2) => (⟨(S.orderEmbOfFin hcard) i,
      Finset.orderEmbOfFin_mem S hcard i⟩ : S)) := by
    intro ⟨y, hy⟩
    have hmem : y ∈ Set.range (S.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]; exact hy
    rcases hmem with ⟨i, rfl⟩; exact ⟨i, rfl⟩
  let e1 : Fin (u + 1 + 2) ≃ S := Equiv.ofBijective
    (fun i => ⟨(S.orderEmbOfFin hcard) i, Finset.orderEmbOfFin_mem S hcard i⟩)
    ⟨fun i j h => (S.orderEmbOfFin hcard).injective (congrArg Subtype.val h), hsurj⟩
  let e2 : Fin (u + 1 + 2) ≃ S := Equiv.ofBijective
    (fun i => ⟨rawNode (u + 1) i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun i j h => hinj (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
      rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩⟩
  refine ⟨e2.trans e1.symm, ?_⟩
  ext i
  exact congrArg Subtype.val (e1.apply_symm_apply (e2 i))

/-! ### Part 5: Explicit algebraic estimates for `rawNode m` -/

private noncomputable def Qpoly (m : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico m (2 * m), (x - bPos j)

private lemma rawNode_lagrange_eval_y1 {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    (lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x =
      ((x + 1) / δSeq m) * (Qpoly m x / Qpoly m (-1 + δSeq m)) := by
  rw [lagrangeBasis_eval]
  have h0_mem : (⟨0, by omega⟩ : Fin (m + 2)) ∈ Finset.univ.erase ⟨1, by omega⟩ :=
    Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h0_mem]
  have hfac0 : (x - rawNode m ⟨0, by omega⟩) / (rawNode m ⟨1, by omega⟩ - rawNode m ⟨0, by omega⟩) =
      (x + 1) / δSeq m := by
    simp only [rawNode, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; ring
  rw [hfac0]
  congr 1
  unfold Qpoly
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_bij (fun i _ => m + (i.val - 2))
  · intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i hi j hj heq
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi hj
    ext; omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    refine ⟨⟨j - m + 2, by omega⟩, ?_, by dsimp; omega⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]; omega
  · intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
    simp only [rawNode, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega,
      show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]

private lemma rawNode_lagrange_eval_y0 {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    (lagrangeBasis (rawNode m) ⟨0, by omega⟩).eval x =
      -((x + 1 - δSeq m) / δSeq m) * (Qpoly m x / Qpoly m (-1)) := by
  rw [lagrangeBasis_eval]
  have h1_mem : (⟨1, by omega⟩ : Fin (m + 2)) ∈ Finset.univ.erase ⟨0, by omega⟩ :=
    Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h1_mem]
  have hfac1 : (x - rawNode m ⟨1, by omega⟩) / (rawNode m ⟨0, by omega⟩ - rawNode m ⟨1, by omega⟩) =
      -((x + 1 - δSeq m) / δSeq m) := by
    simp only [rawNode, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
    have hden : (-1 : ℝ) - (-1 + δSeq m) = -δSeq m := by ring
    rw [hden, div_neg]; ring
  rw [hfac1]
  congr 1
  unfold Qpoly
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_bij (fun i _ => m + (i.val - 2))
  · intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i hi j hj heq
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi hj
    ext; omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    refine ⟨⟨j - m + 2, by omega⟩, ?_, by dsimp; omega⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]; omega
  · intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
    simp only [rawNode, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega, ↓reduceIte]

private lemma abs_Qpoly_neg_one_ge {m : ℕ} : (1 : ℝ) ≤ |Qpoly m (-1)| := by
  unfold Qpoly
  rw [Finset.abs_prod]
  calc (1 : ℝ) = ∏ _j ∈ Finset.Ico m (2 * m), (1 : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.Ico m (2 * m), |-1 - bPos j| := by
        apply Finset.prod_le_prod (fun _ _ => zero_le_one)
        intro j _
        have hb := (bPos_mem_Icc j).1
        rw [abs_of_nonpos (by linarith)]; linarith

private lemma abs_Qpoly_neg_one_add_δ_ge {m : ℕ} (hm : 1 ≤ m) :
    ((3 : ℝ) / 4) ^ m ≤ |Qpoly m (-1 + δSeq m)| := by
  have hδ4 : δSeq m ≤ 1 / 4 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact le_trans (δSeq_bounds hm).1 (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  unfold Qpoly
  rw [Finset.abs_prod]
  calc ((3 : ℝ) / 4) ^ m = ∏ _j ∈ Finset.Ico m (2 * m), ((3 : ℝ) / 4) := by
        rw [Finset.prod_const, Nat.card_Ico, show 2 * m - m = m by omega]
    _ ≤ ∏ j ∈ Finset.Ico m (2 * m), |-1 + δSeq m - bPos j| := by
        apply Finset.prod_le_prod (fun _ _ => by norm_num)
        intro j _
        have hb := (bPos_mem_Icc j).1
        rw [abs_of_nonpos (by linarith)]; linarith

private lemma abs_Qpoly_le {m k : ℕ} (hk : k ∈ Finset.Ico m (2 * m)) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |Qpoly m x| ≤ (2 : ℝ) ^ m * |x - bPos k| := by
  unfold Qpoly
  rw [← Finset.mul_prod_erase _ _ hk, abs_mul, Finset.abs_prod, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc ∏ j ∈ (Finset.Ico m (2 * m)).erase k, |x - bPos j|
    _ ≤ ∏ _j ∈ (Finset.Ico m (2 * m)).erase k, (2 : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro j _
        have hb := bPos_mem_Icc j
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hb.1, hb.2]
    _ = (2 : ℝ) ^ ((Finset.Ico m (2 * m)).erase k).card := Finset.prod_const 2
    _ ≤ (2 : ℝ) ^ m := by
        apply pow_le_pow_right₀ (by norm_num)
        rw [Finset.card_erase_of_mem hk, Nat.card_Ico]; omega

private lemma rawNode_y0_add_y1_bound {m k : ℕ} (hm : 1 ≤ m) (hk : k ∈ Finset.Ico m (2 * m))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |(lagrangeBasis (rawNode m) ⟨0, by omega⟩).eval x +
      (lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ≤
      4 * (m : ℝ) * (6 : ℝ) ^ m * |x - bPos k| := by
  rw [rawNode_lagrange_eval_y0 hm, rawNode_lagrange_eval_y1 hm]
  have hQ0_pos : 0 < |Qpoly m (-1)| := lt_of_lt_of_le zero_lt_one abs_Qpoly_neg_one_ge
  have hQ1_pos : 0 < |Qpoly m (-1 + δSeq m)| :=
    lt_of_lt_of_le (by positivity) (abs_Qpoly_neg_one_add_δ_ge hm)
  have hQ0_ne : Qpoly m (-1) ≠ 0 := abs_pos.mp hQ0_pos
  have hQ1_ne : Qpoly m (-1 + δSeq m) ≠ 0 := abs_pos.mp hQ1_pos
  have hδ_pos := δSeq_pos hm
  have hδ_ne := hδ_pos.ne'
  have halg : -((x + 1 - δSeq m) / δSeq m) * (Qpoly m x / Qpoly m (-1)) +
      ((x + 1) / δSeq m) * (Qpoly m x / Qpoly m (-1 + δSeq m)) =
      Qpoly m x * (1 / Qpoly m (-1) +
        (x + 1) * (Qpoly m (-1) - Qpoly m (-1 + δSeq m)) /
          (δSeq m * Qpoly m (-1) * Qpoly m (-1 + δSeq m))) := by
    field_simp; ring
  rw [halg, abs_mul]
  have hdiff : |Qpoly m (-1) - Qpoly m (-1 + δSeq m)| ≤ (m : ℝ) * (2 : ℝ) ^ m * δSeq m := by
    unfold Qpoly
    have hcard : (Finset.Ico m (2 * m)).card = m := by rw [Nat.card_Ico]; omega
    have h := prod_sub_prod_abs_le (Finset.Ico m (2 * m))
      (fun j => -1 - bPos j) (fun j => -1 + δSeq m - bPos j) 2 (δSeq m) (by norm_num) hδ_pos.le
      (fun j _ => by
        have hb := bPos_mem_Icc j
        have hδ4 : δSeq m ≤ 1 / 4 := by
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          exact le_trans (δSeq_bounds hm).1 (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
        refine ⟨?_, ?_, ?_⟩
        · rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
        · rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
        · have : -1 - bPos j - (-1 + δSeq m - bPos j) = -δSeq m := by ring
          rw [this, abs_neg, abs_of_pos hδ_pos])
    simpa [hcard] using h
  have hterm1 : |1 / Qpoly m (-1)| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one hQ0_pos]; exact abs_Qpoly_neg_one_ge
  have hterm2 : |(x + 1) * (Qpoly m (-1) - Qpoly m (-1 + δSeq m)) /
      (δSeq m * Qpoly m (-1) * Qpoly m (-1 + δSeq m))| ≤ 2 * (m : ℝ) * ((8 : ℝ) / 3) ^ m := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hδ_pos]
    have hx1 : |x + 1| ≤ 2 := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
    have hnum : |x + 1| * |Qpoly m (-1) - Qpoly m (-1 + δSeq m)| ≤ 2 * ((m : ℝ) * (2 : ℝ) ^ m * δSeq m) :=
      mul_le_mul hx1 hdiff (abs_nonneg _) (by norm_num)
    have hden : δSeq m * 1 * ((3 : ℝ) / 4) ^ m ≤ δSeq m * |Qpoly m (-1)| * |Qpoly m (-1 + δSeq m)| := by
      have h1 := mul_le_mul_of_nonneg_left (@abs_Qpoly_neg_one_ge m) hδ_pos.le
      exact mul_le_mul h1 (abs_Qpoly_neg_one_add_δ_ge hm) (by positivity) (by positivity)
    calc |x + 1| * |Qpoly m (-1) - Qpoly m (-1 + δSeq m)| /
          (δSeq m * |Qpoly m (-1)| * |Qpoly m (-1 + δSeq m)|)
      _ ≤ (2 * ((m : ℝ) * (2 : ℝ) ^ m * δSeq m)) / (δSeq m * 1 * ((3 : ℝ) / 4) ^ m) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 2 * (m : ℝ) * ((8 : ℝ) / 3) ^ m := by
          have : ((8 : ℝ) / 3) ^ m = (2 : ℝ) ^ m / ((3 : ℝ) / 4) ^ m := by
            rw [← div_pow]; norm_num
          rw [this]; field_simp
  have hbr : |1 / Qpoly m (-1) + (x + 1) * (Qpoly m (-1) - Qpoly m (-1 + δSeq m)) /
      (δSeq m * Qpoly m (-1) * Qpoly m (-1 + δSeq m))| ≤ 4 * (m : ℝ) * (3 : ℝ) ^ m := by
    have htri := abs_add_le (1 / Qpoly m (-1)) ((x + 1) * (Qpoly m (-1) - Qpoly m (-1 + δSeq m)) /
      (δSeq m * Qpoly m (-1) * Qpoly m (-1 + δSeq m)))
    have h83 : ((8 : ℝ) / 3) ^ m ≤ (3 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3m : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hQ_le := abs_Qpoly_le hk hx
  calc |Qpoly m x| * |1 / Qpoly m (-1) + (x + 1) * (Qpoly m (-1) - Qpoly m (-1 + δSeq m)) /
        (δSeq m * Qpoly m (-1) * Qpoly m (-1 + δSeq m))|
    _ ≤ ((2 : ℝ) ^ m * |x - bPos k|) * (4 * (m : ℝ) * (3 : ℝ) ^ m) :=
        mul_le_mul hQ_le hbr (abs_nonneg _) (by positivity)
    _ = 4 * (m : ℝ) * ((2 : ℝ) * 3) ^ m * |x - bPos k| := by rw [mul_pow]; ring
    _ = 4 * (m : ℝ) * (6 : ℝ) ^ m * |x - bPos k| := by norm_num

private lemma rawNode_other_basis_bound {m : ℕ} (hm : 1 ≤ m)
    {k j : Fin (m + 2)} (hk2 : 2 ≤ k.val) (hj2 : 2 ≤ j.val) (hjk : j ≠ k)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |(lagrangeBasis (rawNode m) j).eval x| ≤
      6 * (2 / gSeq m) ^ m * |x - bPos (m + (k.val - 2))| := by
  rw [lagrangeBasis_eval, Finset.abs_prod]
  have h0_mem : (⟨0, by omega⟩ : Fin (m + 2)) ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; simp at this; omega, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h0_mem]
  have h1_mem : (⟨1, by omega⟩ : Fin (m + 2)) ∈ (Finset.univ.erase j).erase ⟨0, by omega⟩ :=
    Finset.mem_erase.mpr ⟨by simp, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; simp at this; omega, Finset.mem_univ _⟩⟩
  rw [← Finset.mul_prod_erase _ _ h1_mem]
  have hk_mem : k ∈ ((Finset.univ.erase j).erase ⟨0, by omega⟩).erase ⟨1, by omega⟩ := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
    exact ⟨by omega, by omega, by intro h; apply hjk; exact Fin.ext h.symm⟩
  rw [← Finset.mul_prod_erase _ _ hk_mem]
  have hδ4 : δSeq m ≤ 1 / 4 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact le_trans (δSeq_bounds hm).1 (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hbj : rawNode m j = bPos (m + (j.val - 2)) := by
    unfold rawNode; simp only [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, ↓reduceIte]
  have hbk : rawNode m k = bPos (m + (k.val - 2)) := by
    unfold rawNode; simp only [show k.val ≠ 0 by omega, show k.val ≠ 1 by omega, ↓reduceIte]
  have hbj_mem := bPos_mem_Icc (m + (j.val - 2))
  have hfac0 : |(x - rawNode m ⟨0, by omega⟩) / (rawNode m j - rawNode m ⟨0, by omega⟩)| ≤ 2 := by
    rw [hbj]; simp only [rawNode, ↓reduceIte]
    rw [abs_div, abs_of_nonneg (by linarith [hx.1]), abs_of_pos (by linarith [hbj_mem.1])]
    rw [div_le_iff₀ (by linarith [hbj_mem.1])]; linarith [hx.2, hbj_mem.1]
  have hfac1 : |(x - rawNode m ⟨1, by omega⟩) / (rawNode m j - rawNode m ⟨1, by omega⟩)| ≤ 3 := by
    rw [hbj]; simp only [rawNode, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
    rw [abs_div, abs_of_nonneg (by linarith [hx.1, δSeq_pos hm]), abs_of_pos (by linarith [hbj_mem.1])]
    rw [div_le_iff₀ (by linarith [hbj_mem.1])]; linarith [hx.2, hbj_mem.1, δSeq_pos hm]
  have hg_pos := gSeq_pos hm
  have hsep_jk : gSeq m ≤ |rawNode m j - rawNode m k| := by
    rw [hbj, hbk]
    exact (tree_inv m hm).2.2.2.2 _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) (by intro h; apply hjk; ext; omega)
  have hfack : |(x - rawNode m k) / (rawNode m j - rawNode m k)| ≤ (1 / gSeq m) * |x - bPos (m + (k.val - 2))| := by
    rw [hbk, abs_div, div_eq_inv_mul, one_div]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hg_pos (hbk ▸ hsep_jk)) (abs_nonneg _)
  set R := (((Finset.univ.erase j).erase ⟨0, by omega⟩).erase ⟨1, by omega⟩).erase k
  have hR_prod : ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)| ≤ (2 / gSeq m) ^ R.card := by
    calc ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)|
      _ ≤ ∏ _i ∈ R, (2 / gSeq m) := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro i hi
          have hi_ne : i ≠ k ∧ i ≠ ⟨1, by omega⟩ ∧ i ≠ ⟨0, by omega⟩ ∧ i ≠ j := by
            simp only [R, Finset.mem_erase, Finset.mem_univ, and_true] at hi; exact hi
          have hi2 : 2 ≤ i.val := by
            by_contra hlt
            have : i.val = 0 ∨ i.val = 1 := by omega
            rcases this with h0 | h1
            · exact hi_ne.2.2.1 (Fin.ext h0)
            · exact hi_ne.2.1 (Fin.ext h1)
          have hbi : rawNode m i = bPos (m + (i.val - 2)) := by
            unfold rawNode; simp only [show i.val ≠ 0 by omega, show i.val ≠ 1 by omega, ↓reduceIte]
          have hbi_mem := bPos_mem_Icc (m + (i.val - 2))
          have hsep_ji : gSeq m ≤ |rawNode m j - rawNode m i| := by
            rw [hbj, hbi]
            exact (tree_inv m hm).2.2.2.2 _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
              _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) (by intro h; apply hi_ne.2.2.2; ext; omega)
          rw [abs_div]
          have hnum : |x - rawNode m i| ≤ 2 := by
            rw [hbi, abs_le]; constructor <;> linarith [hx.1, hx.2, hbi_mem.1, hbi_mem.2]
          exact div_le_div₀ (by norm_num) hnum hg_pos hsep_ji
      _ = (2 / gSeq m) ^ R.card := Finset.prod_const _
  have hR_card : R.card + 1 ≤ m := by
    have h1 : R.card = m + 2 - 4 := by
      simp only [R, Finset.card_erase_of_mem hk_mem, Finset.card_erase_of_mem h1_mem,
        Finset.card_erase_of_mem h0_mem, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
      omega
    omega
  have h2g_ge : 1 ≤ 2 / gSeq m := by
    rw [one_le_div hg_pos]
    have hg_le : gSeq m ≤ 1 / 4 := by
      unfold gSeq; split_ifs with h1
      · exact le_rfl
      · have := (tree_inv m hm).2.1 (m - 1) (by omega) (by omega); linarith
    linarith
  have hpow : (1 / gSeq m) * (2 / gSeq m) ^ R.card ≤ (2 / gSeq m) ^ m := by
    calc (1 / gSeq m) * (2 / gSeq m) ^ R.card
      _ ≤ (2 / gSeq m) * (2 / gSeq m) ^ R.card := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_right (by norm_num) hg_pos.le
      _ = (2 / gSeq m) ^ (R.card + 1) := (pow_succ' _ _).symm
      _ ≤ (2 / gSeq m) ^ m := pow_le_pow_right₀ h2g_ge hR_card
  have hmul1 : |(x - rawNode m ⟨0, by omega⟩) / (rawNode m j - rawNode m ⟨0, by omega⟩)| *
      |(x - rawNode m ⟨1, by omega⟩) / (rawNode m j - rawNode m ⟨1, by omega⟩)| ≤ 6 := by
    nlinarith [abs_nonneg ((x - rawNode m ⟨0, by omega⟩) / (rawNode m j - rawNode m ⟨0, by omega⟩)),
      abs_nonneg ((x - rawNode m ⟨1, by omega⟩) / (rawNode m j - rawNode m ⟨1, by omega⟩))]
  have hmul2 : |(x - rawNode m k) / (rawNode m j - rawNode m k)| *
      ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)| ≤
      (2 / gSeq m) ^ m * |x - bPos (m + (k.val - 2))| := by
    calc |(x - rawNode m k) / (rawNode m j - rawNode m k)| *
          ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)|
      _ ≤ ((1 / gSeq m) * |x - bPos (m + (k.val - 2))|) * (2 / gSeq m) ^ R.card :=
          mul_le_mul hfack hR_prod (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ = ((1 / gSeq m) * (2 / gSeq m) ^ R.card) * |x - bPos (m + (k.val - 2))| := by ring
      _ ≤ (2 / gSeq m) ^ m * |x - bPos (m + (k.val - 2))| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
  have hprod_nn : 0 ≤ |(x - rawNode m k) / (rawNode m j - rawNode m k)| *
      ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)| :=
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  have hre : |(x - rawNode m ⟨0, by omega⟩) / (rawNode m j - rawNode m ⟨0, by omega⟩)| *
      (|(x - rawNode m ⟨1, by omega⟩) / (rawNode m j - rawNode m ⟨1, by omega⟩)| *
      (|(x - rawNode m k) / (rawNode m j - rawNode m k)| *
        ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)|)) =
      (|(x - rawNode m ⟨0, by omega⟩) / (rawNode m j - rawNode m ⟨0, by omega⟩)| *
       |(x - rawNode m ⟨1, by omega⟩) / (rawNode m j - rawNode m ⟨1, by omega⟩)|) *
      (|(x - rawNode m k) / (rawNode m j - rawNode m k)| *
        ∏ i ∈ R, |(x - rawNode m i) / (rawNode m j - rawNode m i)|) := by ring
  rw [hre]
  calc _ ≤ 6 * ((2 / gSeq m) ^ m * |x - bPos (m + (k.val - 2))|) :=
        mul_le_mul hmul1 hmul2 hprod_nn (by norm_num)
    _ = 6 * (2 / gSeq m) ^ m * |x - bPos (m + (k.val - 2))| := by ring

private lemma interp_error_bound {m : ℕ} (hm : 1 ≤ m) {k_idx : ℕ} (hk : k_idx ∈ Finset.Ico m (2 * m))
    (f : ℝ → ℝ) (B : ℝ) (hB : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f y| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) (hdist : |x - bPos k_idx| ≤ 2 * sSeq m) :
    |(interpPoly (aNodes (m + 2)) f).eval x - f x| ≤
      |f (bPos k_idx) - f x| + B / (2 : ℝ) ^ m +
        |f (-1 + δSeq m) - f (-1)| * |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| := by
  obtain ⟨e, he⟩ := aNodes_equiv_rawNode hm
  rw [← interpPoly_comp_equiv (aNodes (m + 2)) e f, he]
  let k : Fin (m + 2) := ⟨k_idx - m + 2, by simp only [Finset.mem_Ico] at hk; omega⟩
  have hk_pos : rawNode m k = bPos k_idx := by
    simp only [k, rawNode, show k_idx - m + 2 ≠ 0 by omega, show k_idx - m + 2 ≠ 1 by omega, ↓reduceIte]
    congr 1; simp only [Finset.mem_Ico] at hk; omega
  have hsum1 : ∑ i : Fin (m + 2), (lagrangeBasis (rawNode m) i).eval x = 1 :=
    lagrangeBasis_sum_eq_one (by omega) (rawNode_injective hm) x
  let L : Fin (m + 2) → ℝ := fun i => (lagrangeBasis (rawNode m) i).eval x
  have heval : (interpPoly (rawNode m) f).eval x = ∑ i : Fin (m + 2), f (rawNode m i) * L i := by
    simp [interpPoly, L, Polynomial.eval_finsetSum]
  rw [heval]
  let i0 : Fin (m + 2) := ⟨0, by omega⟩
  let i1 : Fin (m + 2) := ⟨1, by omega⟩
  have hki0 : k ≠ i0 := by intro h; have := congrArg Fin.val h; simp [k, i0] at this
  have hki1 : k ≠ i1 := by intro h; have := congrArg Fin.val h; simp [k, i1] at this
  have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  set S_rest := ((Finset.univ.erase k).erase i0).erase i1
  have hsplit : ∀ g : Fin (m + 2) → ℝ,
      ∑ i : Fin (m + 2), g i = g k + g i0 + g i1 + ∑ j ∈ S_rest, g j := by
    intro g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have h0m : i0 ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hki0.symm, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ h0m]
    have h1m : i1 ∈ (Finset.univ.erase k).erase i0 :=
      Finset.mem_erase.mpr ⟨hi01.symm, Finset.mem_erase.mpr ⟨hki1.symm, Finset.mem_univ _⟩⟩
    rw [← Finset.add_sum_erase _ _ h1m]
    ring
  have hLk : L k = 1 - (L i0 + L i1) - ∑ j ∈ S_rest, L j := by
    have := hsplit L; linarith
  have hident : (∑ i : Fin (m + 2), f (rawNode m i) * L i) - f x =
      (f (bPos k_idx) - f x) +
      (∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j) +
      (f (-1) - f (bPos k_idx)) * (L i0 + L i1) +
      (f (-1 + δSeq m) - f (-1)) * L i1 := by
    rw [hsplit (fun i => f (rawNode m i) * L i), hk_pos, hLk]
    have hi0_v : rawNode m i0 = -1 := by simp [i0, rawNode]
    have hi1_v : rawNode m i1 = -1 + δSeq m := by simp [i1, rawNode]
    rw [hi0_v, hi1_v]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hident]
  have hB_nn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by constructor <;> norm_num))
  have hfbk : |f (bPos k_idx)| ≤ B := hB _ (by have := bPos_mem_Icc k_idx; constructor <;> linarith [this.1, this.2])
  have hf_neg1 : |f (-1)| ≤ B := hB (-1) (by constructor <;> norm_num)
  have hrest_bd : |∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j| ≤
      2 * B * ((m : ℝ) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) := by
    calc |∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j|
      _ ≤ ∑ j ∈ S_rest, |(f (rawNode m j) - f (bPos k_idx)) * L j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S_rest, (2 * B) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|) := by
          apply Finset.sum_le_sum; intro j hj
          rw [abs_mul]
          have hj_ne : j ≠ i1 ∧ j ≠ i0 ∧ j ≠ k := by
            simp only [S_rest, Finset.mem_erase, Finset.mem_univ, and_true] at hj; exact hj
          have hj2 : 2 ≤ j.val := by
            by_contra hlt
            have : j.val = 0 ∨ j.val = 1 := by omega
            rcases this with h0 | h1
            · exact hj_ne.2.1 (Fin.ext h0)
            · exact hj_ne.1 (Fin.ext h1)
          have hfj : |f (rawNode m j) - f (bPos k_idx)| ≤ 2 * B := by
            have := hB _ (rawNode_mem_Icc hm j)
            linarith [abs_sub (f (rawNode m j)) (f (bPos k_idx))]
          have hLj := rawNode_other_basis_bound hm (by simp [k]) hj2 hj_ne.2.2 hx
          have hk_eq : m + (k.val - 2) = k_idx := by simp only [k]; simp only [Finset.mem_Ico] at hk; omega
          rw [hk_eq] at hLj
          exact mul_le_mul hfj hLj (abs_nonneg _) (by linarith)
      _ = (S_rest.card : ℝ) * ((2 * B) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * ((2 * B) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) := by
          apply mul_le_mul_of_nonneg_right _ (by have := gSeq_pos hm; positivity)
          have hcard : S_rest.card ≤ m := by
            have h1 : S_rest.card ≤ (Finset.univ : Finset (Fin (m + 2))).card - 2 := by
              have h0m : i0 ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hki0.symm, Finset.mem_univ _⟩
              have h1m : i1 ∈ (Finset.univ.erase k).erase i0 :=
                Finset.mem_erase.mpr ⟨hi01.symm, Finset.mem_erase.mpr ⟨hki1.symm, Finset.mem_univ _⟩⟩
              simp only [S_rest, Finset.card_erase_of_mem h1m, Finset.card_erase_of_mem h0m,
                Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_fin]; omega
            simp only [Finset.card_fin] at h1; omega
          exact_mod_cast hcard
      _ = 2 * B * ((m : ℝ) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) := by ring
  have hy01_bd : |(f (-1) - f (bPos k_idx)) * (L i0 + L i1)| ≤
      2 * B * (4 * (m : ℝ) * (6 : ℝ) ^ m * |x - bPos k_idx|) := by
    rw [abs_mul]
    have hf1 : |f (-1) - f (bPos k_idx)| ≤ 2 * B := by linarith [abs_sub (f (-1)) (f (bPos k_idx))]
    exact mul_le_mul hf1 (rawNode_y0_add_y1_bound hm hk hx) (abs_nonneg _) (by linarith)
  have hs_err : sSeq m ≤ 1 / (4 * 2 ^ m * (6 * (m : ℝ) * (2 / gSeq m) ^ m + 4 * (m : ℝ) * 6 ^ m + 1)) := by
    rw [sSeq_eq hm]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsmooth : 2 * B * ((m : ℝ) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) +
      2 * B * (4 * (m : ℝ) * (6 : ℝ) ^ m * |x - bPos k_idx|) ≤ B / (2 : ℝ) ^ m := by
    set C := 6 * (m : ℝ) * (2 / gSeq m) ^ m + 4 * (m : ℝ) * (6 : ℝ) ^ m
    have hC_nn : 0 ≤ C := by have := gSeq_pos hm; positivity
    have hC_pos : 0 < C + 1 := by linarith
    have h1 : 4 * (2 : ℝ) ^ m * (C + 1) * sSeq m ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hs_err (show 0 ≤ 4 * (2 : ℝ) ^ m * (C + 1) by positivity)
      have heq : 4 * (2 : ℝ) ^ m * (C + 1) * (1 / (4 * 2 ^ m * (C + 1))) = 1 := by field_simp
      linarith
    have h2 : 4 * C * sSeq m ≤ 1 / (2 : ℝ) ^ m := by
      rw [le_div_iff₀ (by positivity)]
      have : 4 * C * sSeq m * (2 : ℝ) ^ m ≤ 4 * (2 : ℝ) ^ m * (C + 1) * sSeq m := by
        have := (sSeq_pos hm).le; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m]
      linarith
    have h3 : 2 * C * |x - bPos k_idx| ≤ 4 * C * sSeq m := by nlinarith
    have h4 : B * (2 * C * |x - bPos k_idx|) ≤ B * (1 / (2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left (le_trans h3 h2) hB_nn
    have hrew : 2 * B * ((m : ℝ) * (6 * (2 / gSeq m) ^ m * |x - bPos k_idx|)) +
        2 * B * (4 * (m : ℝ) * (6 : ℝ) ^ m * |x - bPos k_idx|) = B * (2 * C * |x - bPos k_idx|) := by
      simp only [C]; ring
    rw [hrew]; linarith [show B * (1 / (2 : ℝ) ^ m) = B / (2 : ℝ) ^ m by ring]
  have htri1 := abs_add_le
    ((f (bPos k_idx) - f x) + (∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j) +
      (f (-1) - f (bPos k_idx)) * (L i0 + L i1))
    ((f (-1 + δSeq m) - f (-1)) * L i1)
  have htri2 := abs_add_le
    ((f (bPos k_idx) - f x) + (∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j))
    ((f (-1) - f (bPos k_idx)) * (L i0 + L i1))
  have htri3 := abs_add_le (f (bPos k_idx) - f x) (∑ j ∈ S_rest, (f (rawNode m j) - f (bPos k_idx)) * L j)
  rw [abs_mul] at htri1
  linarith

private lemma y1_small_bound {m k_idx : ℕ} (hm : 1 ≤ m) (hk : k_idx ∈ Finset.Ico m (2 * m))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) (hdist : |x - bPos k_idx| ≤ ρSeq m) :
    |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ≤ 1 / (2 : ℝ) ^ m := by
  have hδ_pos := δSeq_pos hm
  have hρ_pos := ρSeq_pos hm
  rw [rawNode_lagrange_eval_y1 hm, abs_mul, abs_div, abs_div, abs_of_pos hδ_pos]
  have hQ_le := abs_Qpoly_le hk hx
  have hQ1_ge := abs_Qpoly_neg_one_add_δ_ge hm
  have hρ_le : ρSeq m ≤ δSeq m / (4 * (6 : ℝ) ^ m) := by
    rw [ρSeq_eq hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hx1 : |x + 1| ≤ 2 := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
  have h1 : |x + 1| / δSeq m * (|Qpoly m x| / |Qpoly m (-1 + δSeq m)|) ≤
      (2 / δSeq m) * ((2 : ℝ) ^ m * ρSeq m / ((3 : ℝ) / 4) ^ m) := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right hx1 (δSeq_pos hm).le
    · exact div_le_div₀ (by positivity) (le_trans hQ_le (mul_le_mul_of_nonneg_left hdist (by positivity)))
        (by positivity) hQ1_ge
    · positivity
    · positivity
  have h2 : (2 / δSeq m) * ((2 : ℝ) ^ m * ρSeq m / ((3 : ℝ) / 4) ^ m) ≤
      (2 / δSeq m) * ((2 : ℝ) ^ m * (δSeq m / (4 * (6 : ℝ) ^ m)) / ((3 : ℝ) / 4) ^ m) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hρ_le (by positivity)
  have h3 : (2 / δSeq m) * ((2 : ℝ) ^ m * (δSeq m / (4 * (6 : ℝ) ^ m)) / ((3 : ℝ) / 4) ^ m) =
      (1 / 2) * ((4 : ℝ) / 9) ^ m := by
    have hδne := (δSeq_pos hm).ne'
    have hpow : ((4 : ℝ) / 9) ^ m = (2 : ℝ) ^ m / ((6 : ℝ) ^ m * ((3 : ℝ) / 4) ^ m) := by
      rw [← mul_pow, ← div_pow]; norm_num
    rw [hpow]; field_simp; ring
  have h4 : (1 / 2) * ((4 : ℝ) / 9) ^ m ≤ 1 / (2 : ℝ) ^ m := by
    have : ((4 : ℝ) / 9) ^ m ≤ ((1 : ℝ) / 2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    rw [one_div_pow] at this
    have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ m := by positivity
    linarith
  linarith

private lemma y1_right_child_bounds {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx_lo : bPos m + sSeq m ≤ x) (hx_hi : x ≤ bPos m + 5 / 4 * sSeq m) :
    targetM m / 2 ≤ |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ∧
      |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ≤ 10 * targetM m := by
  have hδ_pos := δSeq_pos hm
  rw [rawNode_lagrange_eval_y1 hm, abs_mul, abs_div, abs_div, abs_of_pos hδ_pos]
  have hm_mem : m ∈ Finset.Ico m (2 * m) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hbm := bPos_mem_Icc m
  have hs_pos := sSeq_pos hm
  have hs_gap : sSeq m ≤ gSeq m / (16 * (m : ℝ)) := by
    rw [sSeq_eq hm]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hxb_lo : sSeq m ≤ x - bPos m := by linarith
  have hxb_hi : x - bPos m ≤ 5 / 4 * sSeq m := by linarith
  -- Compare ∏_{j ≠ m} |x - bPos j| to ∏_{j ≠ m} |bPos m - bPos j|
  set Pnum := ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |bPos m - bPos j|
  set Pden := ∏ j ∈ Finset.Ico m (2 * m), (1 + bPos j)
  have hPnum_pos : 0 < Pnum := Finset.prod_pos fun j hj =>
    lt_of_lt_of_le (gSeq_pos hm) ((tree_inv m hm).2.2.2.2 m hm_mem j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj).symm)
  have hPden_pos : 0 < Pden := Finset.prod_pos fun j _ => by linarith [(bPos_mem_Icc j).1]
  have hQ_factor : |Qpoly m x| = |x - bPos m| * ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |x - bPos j| := by
    unfold Qpoly; rw [← Finset.mul_prod_erase _ _ hm_mem, abs_mul, Finset.abs_prod]
  have hprod_lo : (1 / 2) * Pnum ≤ ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |x - bPos j| := by
    have hfac : ∀ j ∈ (Finset.Ico m (2 * m)).erase m,
        (1 - 1 / (2 * (m : ℝ))) * |bPos m - bPos j| ≤ |x - bPos j| := by
      intro j hj
      have hsep := (tree_inv m hm).2.2.2.2 m hm_mem j (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj).symm
      have htri : |bPos m - bPos j| - |x - bPos m| ≤ |x - bPos j| := by
        have := abs_add_le (bPos m - x) (x - bPos j)
        rw [abs_sub_comm (bPos m) x] at this
        have heq : bPos m - x + (x - bPos j) = bPos m - bPos j := by ring
        rw [heq] at this; linarith
      have hxb_bd : |x - bPos m| ≤ (1 / (2 * (m : ℝ))) * |bPos m - bPos j| := by
        rw [abs_of_pos (by linarith)]
        have h1 : 5 / 4 * sSeq m ≤ gSeq m / (2 * (m : ℝ)) := by
          have : 5 / 4 * (gSeq m / (16 * (m : ℝ))) ≤ gSeq m / (2 * (m : ℝ)) := by
            have := (gSeq_pos hm).le; field_simp; nlinarith
          linarith [mul_le_mul_of_nonneg_left hs_gap (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        have h2 : gSeq m / (2 * (m : ℝ)) ≤ (1 / (2 * (m : ℝ))) * |bPos m - bPos j| := by
          rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsep (by positivity)
        linarith
      linarith
    have hcard : ((Finset.Ico m (2 * m)).erase m).card = m - 1 := by
      rw [Finset.card_erase_of_mem hm_mem, Nat.card_Ico]; omega
    have h1m_nn : 0 ≤ 1 - 1 / (2 * (m : ℝ)) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have : 1 / (2 * (m : ℝ)) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hpow_ge : (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (m : ℝ))) ^ (m - 1) := by
      have h1 := one_sub_div_pow_ge_half hm
      have h2 : (1 - 1 / (2 * (m : ℝ))) ^ m =
          (1 - 1 / (2 * (m : ℝ))) ^ (m - 1) * (1 - 1 / (2 * (m : ℝ))) := by
        rw [← pow_succ, show m - 1 + 1 = m by omega]
      rw [h2] at h1
      have hle1 : 1 - 1 / (2 * (m : ℝ)) ≤ 1 := by
        have hpos_t : 0 < 1 / (2 * (m : ℝ)) := by positivity
        linarith
      have hpow_nn : 0 ≤ (1 - 1 / (2 * (m : ℝ))) ^ (m - 1) := pow_nonneg h1m_nn _
      nlinarith
    calc (1 / 2) * Pnum ≤ (1 - 1 / (2 * (m : ℝ))) ^ (m - 1) * Pnum :=
          mul_le_mul_of_nonneg_right hpow_ge hPnum_pos.le
      _ = ∏ j ∈ (Finset.Ico m (2 * m)).erase m, ((1 - 1 / (2 * (m : ℝ))) * |bPos m - bPos j|) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
      _ ≤ ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |x - bPos j| :=
          Finset.prod_le_prod (fun _ _ => mul_nonneg h1m_nn (abs_nonneg _)) hfac
  have hprod_hi : ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |x - bPos j| ≤ 2 * Pnum := by
    have hfac : ∀ j ∈ (Finset.Ico m (2 * m)).erase m,
        |x - bPos j| ≤ (1 + 1 / (2 * (m : ℝ))) * |bPos m - bPos j| := by
      intro j hj
      have hsep := (tree_inv m hm).2.2.2.2 m hm_mem j (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj).symm
      have htri : |x - bPos j| ≤ |bPos m - bPos j| + |x - bPos m| := by
        have := abs_add_le (x - bPos m) (bPos m - bPos j)
        have heq : x - bPos m + (bPos m - bPos j) = x - bPos j := by ring
        rw [heq] at this; linarith
      have hxb_bd : |x - bPos m| ≤ (1 / (2 * (m : ℝ))) * |bPos m - bPos j| := by
        rw [abs_of_pos (by linarith)]
        have h1 : 5 / 4 * sSeq m ≤ gSeq m / (2 * (m : ℝ)) := by
          have : 5 / 4 * (gSeq m / (16 * (m : ℝ))) ≤ gSeq m / (2 * (m : ℝ)) := by
            have := (gSeq_pos hm).le; field_simp; nlinarith
          linarith [mul_le_mul_of_nonneg_left hs_gap (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        have h2 : gSeq m / (2 * (m : ℝ)) ≤ (1 / (2 * (m : ℝ))) * |bPos m - bPos j| := by
          rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsep (by positivity)
        linarith
      linarith
    have hcard : ((Finset.Ico m (2 * m)).erase m).card = m - 1 := by
      rw [Finset.card_erase_of_mem hm_mem, Nat.card_Ico]; omega
    have hpow_le : (1 + 1 / (2 * (m : ℝ))) ^ (m - 1) ≤ 2 := by
      have h1 := one_add_div_pow_le_two hm
      have h2 : (1 + 1 / (2 * (m : ℝ))) ^ m =
          (1 + 1 / (2 * (m : ℝ))) ^ (m - 1) * (1 + 1 / (2 * (m : ℝ))) := by
        rw [← pow_succ, show m - 1 + 1 = m by omega]
      rw [h2] at h1
      have hge1 : 1 ≤ 1 + 1 / (2 * (m : ℝ)) := by
        have hpos_t : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
        linarith
      have hpow_nn : 0 ≤ (1 + 1 / (2 * (m : ℝ))) ^ (m - 1) := by positivity
      nlinarith
    calc ∏ j ∈ (Finset.Ico m (2 * m)).erase m, |x - bPos j|
      _ ≤ ∏ j ∈ (Finset.Ico m (2 * m)).erase m, ((1 + 1 / (2 * (m : ℝ))) * |bPos m - bPos j|) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) hfac
      _ = (1 + 1 / (2 * (m : ℝ))) ^ (m - 1) * Pnum := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
      _ ≤ 2 * Pnum := mul_le_mul_of_nonneg_right hpow_le hPnum_pos.le
  -- Compare |Qpoly m (-1 + δSeq m)| to Pden = ∏ (1 + bPos j)
  have hQ1_le : |Qpoly m (-1 + δSeq m)| ≤ Pden := by
    unfold Qpoly; rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro j _
    have hb := (bPos_mem_Icc j).1
    have hδ4 : δSeq m ≤ 1 / 4 := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      exact le_trans (δSeq_bounds hm).1 (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    rw [abs_of_nonpos (by linarith)]; linarith [δSeq_pos hm]
  have hQ1_ge : (1 / 2) * Pden ≤ |Qpoly m (-1 + δSeq m)| := by
    unfold Qpoly; rw [Finset.abs_prod]
    have hcard : (Finset.Ico m (2 * m)).card = m := by rw [Nat.card_Ico]; omega
    have h1m_nn : 0 ≤ 1 - 1 / (2 * (m : ℝ)) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have : 1 / (2 * (m : ℝ)) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    calc (1 / 2) * Pden ≤ (1 - 1 / (2 * (m : ℝ))) ^ m * Pden :=
          mul_le_mul_of_nonneg_right (one_sub_div_pow_ge_half hm) hPden_pos.le
      _ = ∏ j ∈ Finset.Ico m (2 * m), ((1 - 1 / (2 * (m : ℝ))) * (1 + bPos j)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
      _ ≤ ∏ j ∈ Finset.Ico m (2 * m), |-1 + δSeq m - bPos j| := by
          apply Finset.prod_le_prod (fun j _ => mul_nonneg h1m_nn (by linarith [(bPos_mem_Icc j).1]))
          intro j _
          have hb := (bPos_mem_Icc j).1
          have hδ16 := (δSeq_bounds hm).1
          have hδ_le : δSeq m ≤ (1 / (2 * (m : ℝ))) * (1 + bPos j) := by
            have h1 : 1 / (16 * (m : ℝ)) ≤ 1 / (2 * (m : ℝ)) :=
              div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
            have h2 : (1 / (2 * (m : ℝ))) * 1 ≤ (1 / (2 * (m : ℝ))) * (1 + bPos j) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith
          have hδ4 : δSeq m ≤ 1 / 4 := by
            have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
            exact le_trans hδ16 (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
          rw [abs_of_nonpos (by linarith)]; linarith
  have hx1_lo : 1 ≤ |x + 1| := by rw [abs_of_nonneg (by linarith [hbm.1])]; linarith [hbm.1]
  have hx1_hi : |x + 1| ≤ 2 := by
    have hs18 : sSeq m ≤ 1 / 8 := (tree_inv (m + 1) (by omega)).2.1 m hm (by omega)
    rw [abs_of_nonneg (by linarith [hbm.1])]; linarith [hbm.2]
  have hD_eq : Pnum / Pden = DSeq m := rfl
  have hδ_eq : δSeq m = DSeq m * sSeq m / targetM m := δSeq_eq hm
  have hQ1_pos : 0 < |Qpoly m (-1 + δSeq m)| := lt_of_lt_of_le (by positivity) hQ1_ge
  have hM_pos : 0 < targetM m := lt_of_lt_of_le zero_lt_one (targetM_ge_one m)
  have hD_pos := DSeq_pos hm
  constructor
  · have h1 : (1 / δSeq m) * ((sSeq m * ((1 / 2) * Pnum)) / Pden) ≤
        |x + 1| / δSeq m * (|Qpoly m x| / |Qpoly m (-1 + δSeq m)|) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hx1_lo (δSeq_pos hm).le
      · rw [hQ_factor]
        apply div_le_div₀ (by positivity) _ hQ1_pos hQ1_le
        exact mul_le_mul (by rw [abs_of_pos (by linarith)]; exact hxb_lo) hprod_lo (by positivity) (by positivity)
      · positivity
      · positivity
    have h2 : (1 / δSeq m) * ((sSeq m * ((1 / 2) * Pnum)) / Pden) = targetM m / 2 := by
      rw [hδ_eq, ← hD_eq]; field_simp
    linarith
  · have h1 : |x + 1| / δSeq m * (|Qpoly m x| / |Qpoly m (-1 + δSeq m)|) ≤
        (2 / δSeq m) * (((5 / 4 * sSeq m) * (2 * Pnum)) / ((1 / 2) * Pden)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hx1_hi (δSeq_pos hm).le
      · rw [hQ_factor]
        apply div_le_div₀ (by positivity) _ (by positivity) hQ1_ge
        exact mul_le_mul (by rw [abs_of_pos (by linarith)]; exact hxb_hi) hprod_hi (by positivity) (by positivity)
      · positivity
      · positivity
    have h2 : (2 / δSeq m) * (((5 / 4 * sSeq m) * (2 * Pnum)) / ((1 / 2) * Pden)) = 10 * targetM m := by
      rw [hδ_eq, ← hD_eq]; field_simp; ring
    linarith

/-! ### Part 6: Constructing the branch `x(f)` for any continuous `f` -/

private noncomputable def branchNode (f : ℝ → ℝ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    let v := branchNode f k
    if |f (-1 + δSeq v) - f (-1)| ≤ 1 / (targetM v) ^ 2 then 2 * v + 1 else 2 * v

private lemma branchNode_bounds (f : ℝ → ℝ) (k : ℕ) :
    2 ^ k ≤ branchNode f k ∧ branchNode f k < 2 ^ (k + 1) := by
  induction k with
  | zero => simp [branchNode]
  | succ k ih =>
    simp only [branchNode]
    split_ifs <;> constructor <;> (try rw [pow_succ]) <;> omega

private lemma branchNode_log (f : ℝ → ℝ) (k : ℕ) : Nat.log 2 (branchNode f k) = k := by
  obtain ⟨hlo, hhi⟩ := branchNode_bounds f k
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

private lemma branchNode_pos (f : ℝ → ℝ) (k : ℕ) : 1 ≤ branchNode f k := by
  have := (branchNode_bounds f k).1
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

private lemma branchNode_strictMono (f : ℝ → ℝ) : StrictMono (branchNode f) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp := branchNode_pos f k
  simp only [branchNode]; split_ifs <;> omega

private lemma branchNode_unique_active (f : ℝ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ k : ℕ, branchNode f k ∈ Finset.Ico m (2 * m) := by
  have hex : ∃ k, m ≤ branchNode f k := ⟨m, le_trans (Nat.lt_two_pow_self.le) (branchNode_bounds f m).1⟩
  let k := Nat.find hex
  have hk_ge : m ≤ branchNode f k := Nat.find_spec hex
  refine ⟨k, Finset.mem_Ico.mpr ⟨hk_ge, ?_⟩⟩
  by_cases hk0 : k = 0
  · rw [hk0, branchNode]; omega
  · have hprev : branchNode f (k - 1) < m := lt_of_not_ge (Nat.find_min hex (by omega))
    have hstep : branchNode f k ≤ 2 * branchNode f (k - 1) + 1 := by
      have hk_eq : k = (k - 1) + 1 := by omega
      conv_lhs => rw [hk_eq]
      simp only [branchNode]; split_ifs <;> omega
    omega

private lemma bPos_branch_step (f : ℝ → ℝ) (k : ℕ) :
    bPos (branchNode f (k + 1)) = bPos (branchNode f k) +
      if |f (-1 + δSeq (branchNode f k)) - f (-1)| ≤ 1 / (targetM (branchNode f k)) ^ 2
      then sSeq (branchNode f k) else 0 := by
  have hp := branchNode_pos f k
  unfold bPos
  simp only [branchNode]
  split_ifs
  · exact nodePos_two_mul_add_one sSeq hp
  · rw [add_zero]; exact nodePos_two_mul sSeq hp

private lemma bPos_branch_mono (f : ℝ → ℝ) : Monotone (fun k => bPos (branchNode f k)) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [bPos_branch_step]
  split_ifs
  · linarith [sSeq_pos (branchNode_pos f k)]
  · linarith

private lemma bPos_branch_diff_le (f : ℝ → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    bPos (branchNode f l) - bPos (branchNode f k) ≤ 2 * sSeq (branchNode f k) := by
  have hsum : bPos (branchNode f l) - bPos (branchNode f k) =
      ∑ j ∈ Finset.Ico k l, (bPos (branchNode f (j + 1)) - bPos (branchNode f j)) := by
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ t hkt ih =>
      rw [Finset.sum_Ico_succ_top hkt, ← ih]; ring
  rw [hsum]
  have hsub : (Finset.Ico k l).image (branchNode f) ⊆
      Finset.Ico (branchNode f k) (branchNode f k + (branchNode f l - branchNode f k + 1)) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    simp only [Finset.mem_Ico] at hj ⊢
    have h1 := (branchNode_strictMono f).monotone hj.1
    have h2 := (branchNode_strictMono f).monotone hj.2.le
    omega
  calc ∑ j ∈ Finset.Ico k l, (bPos (branchNode f (j + 1)) - bPos (branchNode f j))
    _ ≤ ∑ j ∈ Finset.Ico k l, sSeq (branchNode f j) := by
        apply Finset.sum_le_sum; intro j _
        rw [bPos_branch_step]; split_ifs
        · linarith
        · linarith [sSeq_pos (branchNode_pos f j)]
    _ = ∑ v ∈ (Finset.Ico k l).image (branchNode f), sSeq v := by
        rw [Finset.sum_image (fun a _ b _ h => (branchNode_strictMono f).injective h)]
    _ ≤ ∑ v ∈ Finset.Ico (branchNode f k) (branchNode f k + (branchNode f l - branchNode f k + 1)), sSeq v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ =>
          (sSeq_pos (by have := (Finset.mem_Ico.mp hv).1; have := branchNode_pos f k; omega)).le)
    _ ≤ 2 * sSeq (branchNode f k) := sSeq_tail_sum (branchNode_pos f k)

theorem prove_main :
    ∃ a : (n : ℕ) → Fin n → ℝ,
      (∀ n, 1 ≤ n → StrictMono (a n) ∧ ∀ i, a n i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
        ∃ x ∈ Set.Icc (-1 : ℝ) 1,
          (∀ M : ℝ, ∃ᶠ n : ℕ in atTop, M ≤ lebesgueFun (a n) x) ∧
          Tendsto (fun n : ℕ => (interpPoly (a n) f).eval x) atTop (𝓝 (f x)) := by
  refine ⟨aNodes, aNodes_valid, fun f hf => ?_⟩
  have hbdd : BddAbove (Set.range (fun k => bPos (branchNode f k))) :=
    ⟨1 / 4, fun y hy => by rcases hy with ⟨k, rfl⟩; exact (bPos_mem_Icc _).2⟩
  set x : ℝ := ⨆ k, bPos (branchNode f k)
  have hx_tend : Tendsto (fun k => bPos (branchNode f k)) atTop (𝓝 x) :=
    tendsto_atTop_ciSup (bPos_branch_mono f) hbdd
  have hx_ge : ∀ k, bPos (branchNode f k) ≤ x := fun k => le_ciSup hbdd k
  have hx_le_add : ∀ k, x ≤ bPos (branchNode f k) + 2 * sSeq (branchNode f k) := by
    intro k
    refine ciSup_le fun l => ?_
    by_cases hkl : k ≤ l
    · linarith [bPos_branch_diff_le f hkl]
    · have := bPos_branch_mono f (le_of_not_ge hkl)
      linarith [sSeq_pos (branchNode_pos f k)]
  have hx_mem : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    refine ⟨le_trans (bPos_mem_Icc _).1 (hx_ge 0), ?_⟩
    have := ciSup_le fun k => (bPos_mem_Icc (branchNode f k)).2
    linarith
  have hx_Icc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx_mem.1], by linarith [hx_mem.2]⟩
  -- Continuity of f at -1 gives ε m = |f (-1 + δSeq m) - f (-1)| → 0
  have hδ_zero : Tendsto (fun m => -1 + δSeq m) atTop (𝓝 (-1 : ℝ)) := by
    have h0 : Tendsto δSeq atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun m => (1 : ℝ) / 2 ^ m) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        rw [Real.norm_eq_abs, abs_of_pos (δSeq_pos hm)]
        exact (δSeq_bounds hm).2
      · simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using tendsto_const_nhds.add h0
  have hδ_mem : ∀ᶠ m in atTop, -1 + δSeq m ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hpos := δSeq_pos hm
    have hle := (δSeq_bounds hm).2
    have h2 : (1 : ℝ) / 2 ^ m ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    exact ⟨by linarith, by linarith⟩
  have hε_zero : Tendsto (fun m => |f (-1 + δSeq m) - f (-1)|) atTop (𝓝 0) := by
    have hf1 : ContinuousWithinAt f (Set.Icc (-1 : ℝ) 1) (-1) :=
      hf (-1) (by constructor <;> norm_num)
    have hcomp := hf1.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_zero hδ_mem)
    simpa [sub_self] using (hcomp.sub (tendsto_const_nhds (x := f (-1)))).abs
  refine ⟨x, hx_Icc, ?_, ?_⟩
  · -- Part A: limsup lebesgueFun (aNodes n) x = ∞
    intro M
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨Mnat, hMnat⟩ := exists_nat_gt (max M 1)
    set target : ℕ := 2 * Mnat + 2
    have hε_ev := (Metric.tendsto_atTop.mp hε_zero) (1 / ((target + 1 : ℕ) : ℝ) ^ 2) (by positivity)
    rcases hε_ev with ⟨N0, hN0⟩
    obtain ⟨k, hk_ge, hk_M⟩ := exists_depth_targetM target (max N N0)
    set m := branchNode f k
    have hm_pos : 1 ≤ m := branchNode_pos f k
    have hm_ge : max N N0 ≤ m := le_trans hk_ge (le_trans (Nat.lt_two_pow_self.le) (branchNode_bounds f k).1)
    have hM_eq : targetM m = ((target + 1 : ℕ) : ℝ) := by
      unfold targetM; rw [branchNode_log f k]; exact hk_M
    have hε_le : |f (-1 + δSeq m) - f (-1)| ≤ 1 / (targetM m) ^ 2 := by
      have h := hN0 m (le_trans (le_max_right N N0) hm_ge)
      rw [Real.dist_eq, sub_zero, abs_abs] at h
      rw [hM_eq]; exact h.le
    have hright : branchNode f (k + 1) = 2 * m + 1 := by
      simp only [branchNode, m, hε_le, ↓reduceIte]
    have h2m1_eq : bPos (2 * m + 1) = bPos m + sSeq m := nodePos_two_mul_add_one sSeq hm_pos
    have hx_lo : bPos m + sSeq m ≤ x := by
      have := hx_ge (k + 1)
      rw [hright, h2m1_eq] at this
      exact this
    have hx_hi : x ≤ bPos m + 5 / 4 * sSeq m := by
      have h1 := hx_le_add (k + 1)
      rw [hright, h2m1_eq] at h1
      have h2 : sSeq (2 * m + 1) ≤ ρSeq m / 4 := sSeq_le_ρSeq_div4 hm_pos (by omega)
      have h3 : ρSeq m ≤ sSeq m / 8 := by rw [ρSeq_eq hm_pos]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hy1_ge := (y1_right_child_bounds hm_pos hx_lo hx_hi).1
    refine ⟨m + 2, by have := le_trans (le_max_left N N0) hm_ge; omega, ?_⟩
    obtain ⟨e, he⟩ := aNodes_equiv_rawNode hm_pos
    rw [← lebesgueFun_comp_equiv (aNodes (m + 2)) e x, he]
    have hleb : |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ≤ lebesgueFun (rawNode m) x :=
      Finset.single_le_sum (f := fun i => |(lagrangeBasis (rawNode m) i).eval x|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hM_lt : M ≤ ((target + 1 : ℕ) : ℝ) / 2 := by
      have h1 : M < (Mnat : ℝ) := lt_of_le_of_lt (le_max_left M 1) hMnat
      have h2 : ((target + 1 : ℕ) : ℝ) = 2 * (Mnat : ℝ) + 3 := by
        simp only [target]; push_cast; ring
      linarith
    rw [hM_eq] at hy1_ge
    linarith
  · -- Part B: Tendsto (fun n => (interpPoly (aNodes n) f).eval x) atTop (𝓝 (f x))
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    have hB_abs : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f y| ≤ B := fun y hy => by
      simpa [Real.norm_eq_abs] using hB y hy
    have hB_nn : 0 ≤ B := le_trans (abs_nonneg _) (hB_abs 0 (by constructor <;> norm_num))
    rw [Metric.tendsto_atTop]
    intro η hη
    -- 1) From continuity of f at x, find δf > 0
    have hfx : ContinuousWithinAt f (Set.Icc (-1 : ℝ) 1) x := hf x hx_Icc
    obtain ⟨δf, hδf_pos, hδf⟩ := Metric.continuousWithinAt_iff.mp hfx (η / 4) (by linarith)
    -- 2) Choose N1 so B / 2^m < η / 4, 2 * sSeq m < δf, |f(-1+δm)-f(-1)| < min (η/4) ((η/40)^2)
    have hs_zero : Tendsto sSeq atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun m => ((1 : ℝ) / 2) ^ m) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        rw [Real.norm_eq_abs, abs_of_pos (sSeq_pos hm)]
        induction m, hm using Nat.le_induction with
        | base =>
          have := (tree_inv 2 (by omega)).2.1 1 le_rfl (by omega); norm_num; linarith
        | succ t ht ih =>
          have hstep := sSeq_le_div32 ht
          have := (sSeq_pos ht).le
          rw [pow_succ]; linarith
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hB_zero : Tendsto (fun m : ℕ => B / (2 : ℝ) ^ m) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [div_eq_mul_inv, one_div_pow] using tendsto_const_nhds.mul h
    have h1 := (Metric.tendsto_atTop.mp hB_zero) (η / 4) (by linarith)
    have h2 := (Metric.tendsto_atTop.mp hs_zero) (δf / 2) (by linarith)
    have h3 := (Metric.tendsto_atTop.mp hε_zero) (min (η / 4) ((η / 40) ^ 2)) (by positivity)
    rcases h1 with ⟨N1, hN1⟩
    rcases h2 with ⟨N2, hN2⟩
    rcases h3 with ⟨N3, hN3⟩
    refine ⟨max (max N1 N2) (max N3 1) + 2, fun n hn => ?_⟩
    set m := n - 2
    have hm_ge1 : 1 ≤ m := by omega
    have hm_N1 : N1 ≤ m := by omega
    have hm_N2 : N2 ≤ m := by omega
    have hm_N3 : N3 ≤ m := by omega
    have hn_eq : m + 2 = n := by omega
    rw [← hn_eq, Real.dist_eq]
    obtain ⟨k, hk_mem⟩ := branchNode_unique_active f hm_ge1
    set v := branchNode f k
    have hv_ge_m : m ≤ v := (Finset.mem_Ico.mp hk_mem).1
    have hdist_le : |x - bPos v| ≤ 2 * sSeq m := by
      have h1' : 0 ≤ x - bPos v := sub_nonneg.mpr (hx_ge k)
      have h2' : x - bPos v ≤ 2 * sSeq v := by linarith [hx_le_add k]
      have h3' : sSeq v ≤ sSeq m := by
        by_cases hvm : v = m
        · rw [hvm]
        · have := sSeq_le_ρSeq_div4 hm_ge1 (by omega : m < v)
          have := (ρSeq_eq hm_ge1)
          have hρs : ρSeq m ≤ sSeq m / 8 := by rw [ρSeq_eq hm_ge1]; exact le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
      rw [abs_of_nonneg h1']; linarith
    have herr := interp_error_bound hm_ge1 hk_mem f B hB_abs hx_mem hdist_le
    have hfb_lt : |f (bPos v) - f x| < η / 4 := by
      have hs_lt : sSeq m < δf / 2 := by
        have h := hN2 m hm_N2
        rwa [Real.dist_eq, sub_zero, abs_of_pos (sSeq_pos hm_ge1)] at h
      have hbv_Icc : bPos v ∈ Set.Icc (-1 : ℝ) 1 := by
        have := bPos_mem_Icc v; exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have hdist_lt : dist (bPos v) x < δf := by
        rw [Real.dist_eq, abs_sub_comm]; linarith
      simpa [Real.dist_eq] using hδf hbv_Icc hdist_lt
    have hB_lt : B / (2 : ℝ) ^ m < η / 4 := by
      have h := hN1 m hm_N1
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    have hε_lt : |f (-1 + δSeq m) - f (-1)| < min (η / 4) ((η / 40) ^ 2) := by
      have h := hN3 m hm_N3
      rwa [Real.dist_eq, sub_zero, abs_abs] at h
    have hlast_le : |f (-1 + δSeq m) - f (-1)| * |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x| ≤ η / 4 := by
      by_cases hcond : v = m ∧ |f (-1 + δSeq m) - f (-1)| ≤ 1 / (targetM m) ^ 2
      · -- Right child at m: |L_1(x)| ≤ 10 * targetM m, and ε_m * targetM m ≤ √(ε_m) < η / 40
        have hright : branchNode f (k + 1) = 2 * m + 1 := by
          simp only [branchNode, show branchNode f k = m from hcond.1, hcond.2, ↓reduceIte]
        have h2m1_eq : bPos (2 * m + 1) = bPos m + sSeq m := nodePos_two_mul_add_one sSeq hm_ge1
        have hx_lo : bPos m + sSeq m ≤ x := by
          have := hx_ge (k + 1)
          rw [hright, h2m1_eq] at this
          exact this
        have hx_hi : x ≤ bPos m + 5 / 4 * sSeq m := by
          have h1' := hx_le_add (k + 1)
          rw [hright, h2m1_eq] at h1'
          have h2' : sSeq (2 * m + 1) ≤ ρSeq m / 4 := sSeq_le_ρSeq_div4 hm_ge1 (by omega)
          have h3' : ρSeq m ≤ sSeq m / 8 := by rw [ρSeq_eq hm_ge1]; exact le_trans (min_le_right _ _) (min_le_left _ _)
          linarith
        have hy1_hi := (y1_right_child_bounds hm_ge1 hx_lo hx_hi).2
        have hε_sq : |f (-1 + δSeq m) - f (-1)| ≤ (η / 40) ^ 2 := le_trans hε_lt.le (min_le_right _ _)
        have hM_pos : 0 < targetM m := lt_of_lt_of_le zero_lt_one (targetM_ge_one m)
        have hεM : |f (-1 + δSeq m) - f (-1)| * targetM m ≤ η / 40 := by
          have hsq : (|f (-1 + δSeq m) - f (-1)| * targetM m) ^ 2 ≤ (η / 40) ^ 2 := by
            have h1' : |f (-1 + δSeq m) - f (-1)| * (targetM m) ^ 2 ≤ 1 := by
              have hc2 := hcond.2
              rwa [le_div_iff₀ (sq_pos_of_pos hM_pos)] at hc2
            calc (|f (-1 + δSeq m) - f (-1)| * targetM m) ^ 2
              _ = |f (-1 + δSeq m) - f (-1)| * (|f (-1 + δSeq m) - f (-1)| * (targetM m) ^ 2) := by ring
              _ ≤ |f (-1 + δSeq m) - f (-1)| * 1 := mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
              _ = |f (-1 + δSeq m) - f (-1)| := mul_one _
              _ ≤ (η / 40) ^ 2 := hε_sq
          nlinarith [mul_nonneg (abs_nonneg (f (-1 + δSeq m) - f (-1))) hM_pos.le]
        calc |f (-1 + δSeq m) - f (-1)| * |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x|
          _ ≤ |f (-1 + δSeq m) - f (-1)| * (10 * targetM m) :=
              mul_le_mul_of_nonneg_left hy1_hi (abs_nonneg _)
          _ = 10 * (|f (-1 + δSeq m) - f (-1)| * targetM m) := by ring
          _ ≤ 10 * (η / 40) := by linarith
          _ = η / 4 := by ring
      · -- Either v > m, or (v = m and went to left child 2*m): in both cases |x - bPos v| ≤ ρSeq m
        have hdist_ρ : |x - bPos v| ≤ ρSeq m := by
          have h1' : 0 ≤ x - bPos v := sub_nonneg.mpr (hx_ge k)
          rw [abs_of_nonneg h1']
          by_cases hvm : v = m
          · have hfail : ¬ (|f (-1 + δSeq m) - f (-1)| ≤ 1 / (targetM m) ^ 2) := fun hc => hcond ⟨hvm, hc⟩
            have hleft : branchNode f (k + 1) = 2 * m := by
              simp only [branchNode, show branchNode f k = m from hvm, hfail, ↓reduceIte]
            have h2m_eq : bPos (2 * m) = bPos m := nodePos_two_mul sSeq hm_ge1
            have h2' := hx_le_add (k + 1)
            rw [hleft, h2m_eq] at h2'
            have h3' : sSeq (2 * m) ≤ ρSeq m / 4 := sSeq_le_ρSeq_div4 hm_ge1 (by omega)
            rw [hvm]; linarith [ρSeq_pos hm_ge1]
          · have h2' := hx_le_add k
            have h3' : sSeq v ≤ ρSeq m / 4 := sSeq_le_ρSeq_div4 hm_ge1 (by omega)
            linarith [ρSeq_pos hm_ge1]
        have hy1_sm := y1_small_bound hm_ge1 hk_mem hx_mem hdist_ρ
        have h2m : (1 : ℝ) / (2 : ℝ) ^ m ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        have hε4 : |f (-1 + δSeq m) - f (-1)| ≤ η / 4 := le_trans hε_lt.le (min_le_left _ _)
        calc |f (-1 + δSeq m) - f (-1)| * |(lagrangeBasis (rawNode m) ⟨1, by omega⟩).eval x|
          _ ≤ (η / 4) * 1 := mul_le_mul hε4 (le_trans hy1_sm h2m) (abs_nonneg _) (by linarith)
          _ = η / 4 := mul_one _
    linarith

end OMA.P_erdos_671

theorem OMA.solution : type_of% @OMA.S_erdos_671.main :=
  OMA.P_erdos_671.prove_main
