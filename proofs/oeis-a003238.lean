import OMAStatements.S_oeis_a003238
import Mathlib.Tactic

namespace OMA.S_oeis_a003238_proof

open OMA.S_oeis_a003238 Filter Asymptotics

private lemma size_pos (ds : List ℕ) : 1 ≤ size ds := by
  cases ds with
  | nil => simp [size]
  | cons d t => simp [size]

private lemma size_ge_one (ds : List ℕ) (h : ∀ d ∈ ds, 1 ≤ d) : ds.length < size ds := by
  induction ds with
  | nil => simp [size]
  | cons d t ih =>
    have hd : 1 ≤ d := h d (by simp)
    have ht : t.length < size t := ih fun x hx => h x (by simp [hx])
    simp only [List.length_cons, size]
    nlinarith [size_pos t]

private lemma mem_le_size (ds : List ℕ) (h : ∀ d ∈ ds, 1 ≤ d) : ∀ d ∈ ds, d ≤ size ds := by
  induction ds with
  | nil => simp
  | cons x t ih =>
    intro d hd
    have hx : 1 ≤ x := h x (by simp)
    simp only [List.mem_cons] at hd
    simp only [size]
    rcases hd with rfl | hmem
    · nlinarith [size_pos t]
    · have ht := ih (fun y hy => h y (by simp [hy])) d hmem
      nlinarith

private lemma size_replicate_one (k : ℕ) (ds : List ℕ) :
    size (List.replicate k 1 ++ ds) = k + size ds := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, size, one_mul, ih]
    omega

private def mkTail : List ℕ → List ℕ
  | [] => []
  | c :: cs => 2 :: (List.replicate c 1 ++ mkTail cs)

private def mkList (c₀ : ℕ) (cs : List ℕ) : List ℕ :=
  List.replicate c₀ 1 ++ mkTail cs

private lemma mkTail_mem (cs : List ℕ) : ∀ d ∈ mkTail cs, d = 1 ∨ d = 2 := by
  induction cs with
  | nil => simp [mkTail]
  | cons c t ih =>
    intro d hd
    simp only [mkTail, List.mem_cons, List.mem_append, List.mem_replicate] at hd
    rcases hd with rfl | ⟨_, rfl⟩ | ht
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact ih d ht

private lemma mkList_mem (c₀ : ℕ) (cs : List ℕ) : ∀ d ∈ mkList c₀ cs, d = 1 ∨ d = 2 := by
  intro d hd
  simp only [mkList, List.mem_append, List.mem_replicate] at hd
  rcases hd with ⟨_, rfl⟩ | ht
  · exact Or.inl rfl
  · exact mkTail_mem cs d ht

private def wsum : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, c :: cs => p * c + wsum (2 * p) cs

private lemma wsum_two_mul (p : ℕ) (cs : List ℕ) :
    wsum (2 * p) cs = 2 * wsum p cs := by
  induction cs generalizing p with
  | nil => simp [wsum]
  | cons c t ih =>
    simp only [wsum, ih]
    ring

private lemma mkTail_size (cs : List ℕ) :
    size (mkTail cs) = (2 ^ (cs.length + 1) - 1) + wsum 2 cs := by
  induction cs with
  | nil => simp [mkTail, size, wsum]
  | cons c t ih =>
    simp only [mkTail, size, size_replicate_one, ih, wsum, wsum_two_mul, List.length_cons]
    have hpow : 1 ≤ 2 ^ (t.length + 1) := Nat.one_le_pow _ _ (by omega)
    have hpow2 : 2 ^ (t.length + 1 + 1) = 2 * 2 ^ (t.length + 1) := by ring
    omega

private lemma wsum_ofFn (k p : ℕ) (g : Fin k → ℕ) :
    wsum p (List.ofFn g) = ∑ i : Fin k, p * 2 ^ i.1 * g i := by
  induction k generalizing p with
  | zero => simp [wsum, List.ofFn_zero]
  | succ k ih =>
    rw [List.ofFn_succ, wsum, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ']
    ring

private lemma mkList_size (c₀ : ℕ) (cs : List ℕ) :
    size (mkList c₀ cs) = c₀ + size (mkTail cs) :=
  size_replicate_one c₀ (mkTail cs)

private lemma replicate_one_head_ne_inj {a b : ℕ} {xs ys : List ℕ}
    (hx : xs = [] ∨ xs.head? = some 2) (hy : ys = [] ∨ ys.head? = some 2)
    (h : List.replicate a 1 ++ xs = List.replicate b 1 ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact ⟨rfl, by simpa using h⟩
    | succ b =>
      exfalso
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
      rcases hx with rfl | hx
      · cases h
      · cases xs with
        | nil => simp at hx
        | cons x xs' =>
          simp only [List.head?_cons, Option.some.injEq] at hx
          simp only [List.cons.injEq] at h
          omega
  | succ a ih =>
    cases b with
    | zero =>
      exfalso
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
      rcases hy with rfl | hy
      · cases h
      · cases ys with
        | nil => simp at hy
        | cons y ys' =>
          simp only [List.head?_cons, Option.some.injEq] at hy
          simp only [List.cons.injEq] at h
          omega
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
      rcases ih h.2 with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

private lemma mkTail_head (cs : List ℕ) : mkTail cs = [] ∨ (mkTail cs).head? = some 2 := by
  cases cs <;> simp [mkTail]

private lemma mkTail_inj : Function.Injective mkTail := by
  intro cs₁
  induction cs₁ with
  | nil =>
    intro cs₂ h
    cases cs₂ <;> simp [mkTail] at h ⊢
  | cons c₁ t₁ ih =>
    intro cs₂ h
    cases cs₂ with
    | nil => simp [mkTail] at h
    | cons c₂ t₂ =>
      simp only [mkTail, List.cons.injEq] at h
      rcases replicate_one_head_ne_inj (mkTail_head t₁) (mkTail_head t₂) h.2 with ⟨rfl, ht⟩
      rw [ih ht]

private lemma mkList_inj {c₀₁ c₀₂ : ℕ} {cs₁ cs₂ : List ℕ}
    (h : mkList c₀₁ cs₁ = mkList c₀₂ cs₂) : c₀₁ = c₀₂ ∧ cs₁ = cs₂ := by
  rcases replicate_one_head_ne_inj (mkTail_head cs₁) (mkTail_head cs₂) h with ⟨rfl, ht⟩
  exact ⟨rfl, mkTail_inj ht⟩

private lemma a_eq_card_sigma (n : ℕ) :
    a n = Fintype.card
      (Σ k : Fin n, {f : Fin k.1 → Fin n // size (List.ofFn fun i => (f i : ℕ) + 1) = n}) := by
  rw [Fintype.card_sigma, a, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]

private def listToSigma {n : ℕ} (ds : List ℕ) (hlen : ds.length < n)
    (hbd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ n) (hsz : size ds = n) :
    Σ k : Fin n, {f : Fin k.1 → Fin n // size (List.ofFn fun i => (f i : ℕ) + 1) = n} :=
  ⟨⟨ds.length, hlen⟩, ⟨fun i => ⟨ds[i.1]'i.isLt - 1, by
    have h1 := (hbd ds[i.1] (List.getElem_mem i.isLt)).1
    have h2 := (hbd ds[i.1] (List.getElem_mem i.isLt)).2
    omega⟩, by
    have hlist : (List.ofFn fun i : Fin ds.length => (ds[i.1]'i.isLt - 1 : ℕ) + 1) = ds := by
      refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
      simp only [List.getElem_ofFn]
      have h1 := (hbd ds[j] (List.getElem_mem hj2)).1
      omega
    simpa [hlist] using hsz⟩⟩

private def sigmaToList {n : ℕ}
    (x : Σ k : Fin n, {f : Fin k.1 → Fin n // size (List.ofFn fun i => (f i : ℕ) + 1) = n}) :
    List ℕ :=
  List.ofFn fun i => (x.2.1 i : ℕ) + 1

private lemma sigmaToList_listToSigma {n : ℕ} (ds : List ℕ) (hlen : ds.length < n)
    (hbd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ n) (hsz : size ds = n) :
    sigmaToList (listToSigma ds hlen hbd hsz) = ds := by
  refine List.ext_getElem (by simp [sigmaToList, listToSigma]) fun j hj1 hj2 => ?_
  simp only [sigmaToList, listToSigma, List.getElem_ofFn]
  have h1 := (hbd ds[j] (List.getElem_mem hj2)).1
  omega

private lemma add_one_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ']
    omega

private lemma two_mul_lt_two_pow_L (m : ℕ) : 2 * m < 2 ^ (m / 5 + 4) := by
  have h1 : 2 * m < 10 * (m / 5 + 1) := by omega
  have h2 : m / 5 + 1 ≤ 2 ^ (m / 5) := add_one_le_two_pow (m / 5)
  have h3 : 10 * (m / 5 + 1) ≤ 16 * 2 ^ (m / 5) := by nlinarith
  have h4 : 16 * 2 ^ (m / 5) = 2 ^ (m / 5 + 4) := by
    rw [pow_add, show (2 ^ 4 : ℕ) = 16 by decide, mul_comm]
  omega

private lemma two_mul_sum_range_id (k : ℕ) :
    2 * ∑ i ∈ Finset.range k, i = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring

private lemma a_pow_three_mul_ge (m : ℕ) (hm : 55 ≤ m) :
    2 ^ (∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - (m / 5 + 5))) ≤ a (2 ^ (3 * m)) := by
  let L := m / 5 + 5
  let n := 2 ^ (3 * m)
  let Tup := (i : Fin (2 * m)) → Fin (2 ^ (3 * m - (i.1 + 1) - L))
  have hL_le : 2 * m + L ≤ 3 * m := by omega
  have htail_bound : ∀ c : Tup, size (mkTail (List.ofFn fun i => (c i).1)) ≤ n := by
    intro c
    rw [mkTail_size, List.length_ofFn, wsum_ofFn]
    have hsum_le :
        (∑ i : Fin (2 * m), 2 * 2 ^ i.1 * (c i).1) ≤ (2 * m) * 2 ^ (3 * m - L) := by
      calc
        (∑ i : Fin (2 * m), 2 * 2 ^ i.1 * (c i).1)
          ≤ ∑ _i : Fin (2 * m), 2 ^ (3 * m - L) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi : i.1 + 1 + L ≤ 3 * m := by omega
            have hci : (c i).1 < 2 ^ (3 * m - (i.1 + 1) - L) := (c i).isLt
            have hmul : 2 * 2 ^ i.1 * (c i).1 ≤ 2 ^ (i.1 + 1) * 2 ^ (3 * m - (i.1 + 1) - L) := by
              rw [pow_succ']
              exact Nat.mul_le_mul_left _ (Nat.le_of_lt hci)
            rwa [← pow_add, show i.1 + 1 + (3 * m - (i.1 + 1) - L) = 3 * m - L by omega] at hmul
        _ = (2 * m) * 2 ^ (3 * m - L) := by simp
    have hpow_L : (2 * m) * 2 ^ (3 * m - L) ≤ 2 ^ (3 * m - 1) := by
      have h2m : 2 * m ≤ 2 ^ (L - 1) := Nat.le_of_lt (by simpa [L] using two_mul_lt_two_pow_L m)
      calc
        (2 * m) * 2 ^ (3 * m - L) ≤ 2 ^ (L - 1) * 2 ^ (3 * m - L) :=
          Nat.mul_le_mul_right _ h2m
        _ = 2 ^ (L - 1 + (3 * m - L)) := (pow_add _ _ _).symm
        _ = 2 ^ (3 * m - 1) := by congr 1; omega
    have hpow2m : 2 ^ (2 * m + 1) ≤ 2 ^ (3 * m - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hn_eq : n = 2 ^ (3 * m - 1) + 2 ^ (3 * m - 1) := by
      calc
        n = 2 ^ ((3 * m - 1) + 1) := by dsimp only [n]; congr 1; omega
        _ = 2 ^ (3 * m - 1) * 2 := pow_succ _ _
        _ = 2 ^ (3 * m - 1) + 2 ^ (3 * m - 1) := by ring
    omega
  let toSig : Tup →
      Σ k : Fin n, {f : Fin k.1 → Fin n // size (List.ofFn fun i => (f i : ℕ) + 1) = n} :=
    fun c =>
      let cs := List.ofFn fun i => (c i).1
      let c₀ := n - size (mkTail cs)
      let ds := mkList c₀ cs
      have hsz : size ds = n := by
        dsimp only [ds, c₀]
        rw [mkList_size]
        exact Nat.sub_add_cancel (htail_bound c)
      have hbd1 : ∀ d ∈ ds, 1 ≤ d := fun d hd => by
        rcases mkList_mem c₀ cs d hd with rfl | rfl <;> omega
      have hbd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ n := fun d hd =>
        ⟨hbd1 d hd, hsz ▸ mem_le_size ds hbd1 d hd⟩
      have hlen : ds.length < n := hsz ▸ size_ge_one ds hbd1
      listToSigma ds hlen hbd hsz
  have hinj : Function.Injective toSig := by
    intro c₁ c₂ heq
    have hlist :
        mkList (n - size (mkTail (List.ofFn fun i => (c₁ i).1))) (List.ofFn fun i => (c₁ i).1) =
          mkList (n - size (mkTail (List.ofFn fun i => (c₂ i).1))) (List.ofFn fun i => (c₂ i).1) := by
      have hs := congrArg sigmaToList heq
      dsimp only [toSig] at hs
      rwa [sigmaToList_listToSigma, sigmaToList_listToSigma] at hs
    have hcs := (mkList_inj hlist).2
    funext i
    exact Fin.ext (congrFun (List.ofFn_injective hcs) i)
  have hcard : Fintype.card Tup ≤ a n := by
    rw [a_eq_card_sigma]
    exact Fintype.card_le_of_injective toSig hinj
  have hcard_eq :
      Fintype.card Tup = 2 ^ ∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L) := by
    simp only [Tup, Fintype.card_pi, Fintype.card_fin]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rwa [← hcard_eq]

private lemma exp_sum_ge (m : ℕ) (hm : 55 ≤ m) :
    17 * m ^ 2 ≤ 5 * ∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - (m / 5 + 5)) := by
  let L := m / 5 + 5
  have hsum_int :
      ((∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L) : ℕ) : ℤ) =
        ∑ i : Fin (2 * m), ((3 * m : ℤ) - (i.1 : ℤ) - 1 - (L : ℤ)) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : i.1 + 1 + L ≤ 3 * m := by omega
    omega
  have hid : 2 * (∑ i : Fin (2 * m), (i.1 : ℤ)) = (2 * m : ℤ) * (2 * m - 1) := by
    have h1 := two_mul_sum_range_id (2 * m)
    have h2 : (∑ i : Fin (2 * m), i.1) = ∑ i ∈ Finset.range (2 * m), i := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [← h2] at h1
    have h3 : (2 * ∑ i : Fin (2 * m), i.1 : ℕ) = 2 * m * (2 * m - 1) := h1
    zify [show 1 ≤ 2 * m by omega] at h3
    linarith
  have hsum_eval :
      2 * ((∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L) : ℕ) : ℤ) =
        2 * (2 * m : ℤ) * (3 * m - 1 - L : ℤ) - (2 * m : ℤ) * (2 * m - 1) := by
    rw [hsum_int, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    linarith [hid]
  have hL_bound : 5 * (L : ℤ) ≤ (m : ℤ) + 25 := by
    have hdiv : 5 * (m / 5) ≤ m := by omega
    zify at hdiv
    dsimp only [L]
    push_cast
    linarith
  have hm_z : (55 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have h10 :
      34 * (m : ℤ) ^ 2 ≤
        10 * ((∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L) : ℕ) : ℤ) := by
    have hmul1 : 0 ≤ (m : ℤ) * ((m : ℤ) + 25 - 5 * (L : ℤ)) :=
      mul_nonneg hm0 (sub_nonneg.mpr hL_bound)
    have hmul2 : 0 ≤ (m : ℤ) * ((m : ℤ) - 55) :=
      mul_nonneg hm0 (sub_nonneg.mpr hm_z)
    nlinarith
  have hgoal :
      (17 : ℤ) * (m : ℤ) ^ 2 ≤
        5 * ((∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L) : ℕ) : ℤ) := by
    linarith
  change 17 * m ^ 2 ≤ 5 * ∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - L)
  exact_mod_cast hgoal

end OMA.S_oeis_a003238_proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003238.main) := by
  rintro ⟨c, hc0, hc1, hequiv⟩
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (OMA.S_oeis_a003238.a n : ℝ) - c * Real.log (n : ℝ) ^ 2‖ ≤
        (0.01 : ℝ) * ‖c * Real.log (n : ℝ) ^ 2‖ :=
    hequiv.isLittleO.bound (by positivity)
  rw [Filter.eventually_atTop] at hbound
  rcases hbound with ⟨N, hN⟩
  let m := max N 55
  have hm55 : 55 ≤ m := le_max_right N 55
  have hmN : N ≤ m := le_max_left N 55
  let n := 2 ^ (3 * m)
  have hm_le_n : m ≤ n := by
    have h1 := OMA.S_oeis_a003238_proof.add_one_le_two_pow (3 * m)
    dsimp only [n]
    omega
  have hnN : N ≤ n := le_trans hmN hm_le_n
  have hbn := hN n hnN
  let S := ∑ i : Fin (2 * m), (3 * m - (i.1 + 1) - (m / 5 + 5))
  have ha_ge : 2 ^ S ≤ OMA.S_oeis_a003238.a n :=
    OMA.S_oeis_a003238_proof.a_pow_three_mul_ge m hm55
  have ha_pos : (0 : ℝ) < (OMA.S_oeis_a003238.a n : ℝ) := by
    have h2S : 0 < 2 ^ S := pow_pos (by omega) S
    exact_mod_cast lt_of_lt_of_le h2S ha_ge
  have h2S_pos : (0 : ℝ) < ((2 ^ S : ℕ) : ℝ) := by positivity
  have hlog_a : (S : ℝ) * Real.log 2 ≤ Real.log (OMA.S_oeis_a003238.a n : ℝ) := by
    have hmono : Real.log ((2 ^ S : ℕ) : ℝ) ≤ Real.log (OMA.S_oeis_a003238.a n : ℝ) :=
      Real.log_le_log h2S_pos (by exact_mod_cast ha_ge)
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hmono
  have hS_real : (17 / 5 : ℝ) * (m : ℝ) ^ 2 ≤ (S : ℝ) := by
    have hSi : 17 * m ^ 2 ≤ 5 * S := OMA.S_oeis_a003238_proof.exp_sum_ge m hm55
    have hSr : (17 : ℝ) * (m : ℝ) ^ 2 ≤ 5 * (S : ℝ) := by exact_mod_cast hSi
    linarith
  have hlog_n : Real.log (n : ℝ) = (3 * (m : ℝ)) * Real.log 2 := by
    dsimp only [n]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    ring
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by linarith)
  have hlog2_lt : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by linarith)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hrhs_nonneg : 0 ≤ c * Real.log (n : ℝ) ^ 2 := by positivity
  have hnorm_rhs : ‖c * Real.log (n : ℝ) ^ 2‖ = c * Real.log (n : ℝ) ^ 2 :=
    Real.norm_of_nonneg hrhs_nonneg
  rw [hnorm_rhs, Real.norm_eq_abs, abs_le] at hbn
  have hupper : Real.log (OMA.S_oeis_a003238.a n : ℝ) ≤ (1.01 : ℝ) * (c * Real.log (n : ℝ) ^ 2) := by
    linarith [hbn.2]
  have hchain : (17 / 5 : ℝ) * (m : ℝ) ^ 2 * Real.log 2 ≤
      (1.01 : ℝ) * c * 9 * (m : ℝ) ^ 2 * (Real.log 2) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hS_real (le_of_lt hlog2_pos)
    have h2 : c * Real.log (n : ℝ) ^ 2 = c * 9 * (m : ℝ) ^ 2 * (Real.log 2) ^ 2 := by
      rw [hlog_n]
      ring
    linarith [hlog_a, hupper]
  have hpos_div : 0 < (m : ℝ) ^ 2 * Real.log 2 := by positivity
  have hdiv : (17 / 5 : ℝ) ≤ (1.01 : ℝ) * c * 9 * Real.log 2 := by
    nlinarith
  have hbad : (1.01 : ℝ) * c * 9 * Real.log 2 < (17 / 5 : ℝ) := by
    have h1 : c * Real.log 2 < 0.5 * 0.7 := by nlinarith
    nlinarith
  linarith
