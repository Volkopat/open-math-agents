import OMAStatements.S_oeis_a008278

/-!
# OEIS A008278

Gus Wiseman's divisor interpretation of the reflected Stirling triangle is recorded
in OEIS A008278, https://oeis.org/A008278 (OEIS, CC BY-SA 4.0).
The proof uses its equivalent description by bounded exponent vectors.
Credit: @grp06.
-/

open scoped BigOperators

namespace OMA.S_oeis_a008278

private abbrev Exponents (n : ℕ) := ∀ i : Fin n, Fin (i.val + 1)

private def exponent {n : ℕ} (f : Exponents n) (i : Fin n) : ℕ := (f i).val

private def active {n : ℕ} (f : Exponents n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => exponent f i ≠ 0)

private theorem mem_active {n : ℕ} (f : Exponents n) (i : Fin n) :
    i ∈ active f ↔ exponent f i ≠ 0 := by
  simp [active]

private def distinct {n : ℕ} (f : Exponents n) : Prop :=
  Set.InjOn (exponent f) (active f : Set (Fin n))

private theorem distinct_iff {n : ℕ} {f : Exponents n} :
    distinct f ↔
      ∀ i j : Fin n, exponent f i ≠ 0 → exponent f j ≠ 0 →
        exponent f i = exponent f j → i = j := by
  constructor
  · intro h i j hi hj he
    exact h ((mem_active f i).2 hi) ((mem_active f j).2 hj) he
  · intro h i hi j hj he
    exact h i j ((mem_active f i).1 hi) ((mem_active f j).1 hj) he

private def Config (n t : ℕ) :=
  {f : Exponents n // (active f).card = t ∧ distinct f}

private noncomputable instance (n t : ℕ) : Fintype (Config n t) := by
  classical
  unfold Config
  infer_instance

private def append {n : ℕ} (f : Exponents n) (a : Fin (n + 1)) : Exponents (n + 1) :=
  @Fin.snoc n (fun i => Fin (i.val + 1)) f a

private theorem append_at_old {n : ℕ} (f : Exponents n) (a : Fin (n + 1)) (i : Fin n) :
    exponent (append f a) i.castSucc = exponent f i := by
  simp only [exponent, append, Fin.snoc_castSucc]

private theorem append_at_new {n : ℕ} (f : Exponents n) (a : Fin (n + 1)) :
    exponent (append f a) (Fin.last n) = a.val := by
  simp only [exponent, append, Fin.snoc_last]

private theorem append_eq_iff {n : ℕ} {f g : Exponents n} {a b : Fin (n + 1)} :
    append f a = append g b ↔ f = g ∧ a = b := by
  unfold append
  exact Fin.snoc_inj

private theorem last_notMem_map {n : ℕ} (s : Finset (Fin n)) :
    Fin.last n ∉ s.map Fin.castSuccEmb := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  exact Fin.castSucc_ne_last i hi

private theorem card_active_append {n : ℕ} (f : Exponents n) (a : Fin (n + 1)) :
    (active (append f a)).card = (active f).card + if a.val = 0 then 0 else 1 := by
  classical
  let old := (active f).map Fin.castSuccEmb
  have hn : Fin.last n ∉ old := last_notMem_map _
  have hactive : active (append f a) = if a.val = 0 then old else insert (Fin.last n) old := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · by_cases h : a.val = 0 <;> simp [h, mem_active, append_at_new, hn]
    · have hm : j.castSucc ∈ old ↔ j ∈ active f := Finset.mem_map' Fin.castSuccEmb
      by_cases h : a.val = 0
      · simp only [h, if_true, hm, mem_active, append_at_old]
      · simp only [h, if_false, Finset.mem_insert, Fin.castSucc_ne_last j, false_or, hm,
          mem_active, append_at_old]
  have hold : old.card = (active f).card := Finset.card_map _
  by_cases h : a.val = 0
  · rw [hactive, if_pos h, if_pos h, hold, Nat.add_zero]
  · rw [hactive, if_neg h, if_neg h, Finset.card_insert_of_notMem hn, hold]

private def used {n : ℕ} (f : Exponents n) : Finset ℕ :=
  (active f).image (exponent f)

private theorem mem_used {n : ℕ} (f : Exponents n) (v : ℕ) :
    v ∈ used f ↔ ∃ i : Fin n, exponent f i ≠ 0 ∧ exponent f i = v := by
  simp only [used, Finset.mem_image, mem_active]

private theorem distinct_append {n : ℕ} (f : Exponents n) (a : Fin (n + 1)) :
    distinct (append f a) ↔ distinct f ∧ (a.val ≠ 0 → a.val ∉ used f) := by
  simp only [distinct_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hi hj he
      have hij : i.castSucc = j.castSucc := by
        apply h
        · simpa only [append_at_old] using hi
        · simpa only [append_at_old] using hj
        · simpa only [append_at_old] using he
      exact Fin.castSucc_injective n hij
    · intro ha hu
      obtain ⟨i, hi, he⟩ := (mem_used f a.val).1 hu
      apply Fin.castSucc_ne_last i
      apply h
      · simpa only [append_at_old] using hi
      · simpa only [append_at_new] using ha
      · simpa only [append_at_old, append_at_new] using he
  · rintro ⟨hf, ha⟩ i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _ _ _
        rfl
      · simp only [append_at_new, append_at_old]
        intro hnew hold he
        exact (ha hnew ((mem_used f a.val).2 ⟨j, hold, he.symm⟩)).elim
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [append_at_new, append_at_old]
        intro hold hnew he
        exact (ha hnew ((mem_used f a.val).2 ⟨i, hold, he⟩)).elim
      · simp only [append_at_old]
        intro hi hj he
        exact congrArg Fin.castSucc (hf i j hi hj he)

private def available {n : ℕ} (f : Exponents n) : Finset ℕ :=
  Finset.Icc 1 n \ used f

private theorem mem_available {n : ℕ} (f : Exponents n) (v : ℕ) :
    v ∈ available f ↔ (1 ≤ v ∧ v ≤ n) ∧ v ∉ used f := by
  simp only [available, Finset.mem_sdiff, Finset.mem_Icc]

private theorem card_available {n t : ℕ} (f : Config n t) :
    (available f.1).card = n - t := by
  have hsub : used f.1 ⊆ Finset.Icc 1 n := by
    intro v hv
    obtain ⟨i, hi, he⟩ := (mem_used f.1 v).1 hv
    have hb : exponent f.1 i < i.val + 1 := (f.1 i).isLt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hu : (used f.1).card = t :=
    (Finset.card_image_of_injOn f.2.2).trans f.2.1
  unfold available
  rw [Finset.card_sdiff_of_subset hsub, hu, Nat.card_Icc]
  simp

private def positiveEntry {n : ℕ} {f : Exponents n} (a : ↥(available f)) : Fin (n + 1) :=
  ⟨a.val, Nat.lt_succ_of_le ((mem_available f a.val).1 a.property).1.2⟩

private theorem positiveEntry_ne_zero {n : ℕ} {f : Exponents n} (a : ↥(available f)) :
    (positiveEntry a).val ≠ 0 :=
  Nat.ne_of_gt ((mem_available f a.val).1 a.property).1.1

private def extendZero {n t : ℕ} (f : Config n (t + 1)) : Config (n + 1) (t + 1) :=
  ⟨append f.1 0, by
    constructor
    · rw [card_active_append, if_pos (show (0 : Fin (n + 1)).val = 0 from rfl), Nat.add_zero]
      exact f.2.1
    · exact (distinct_append _ _).2 ⟨f.2.2, fun h => (h rfl).elim⟩⟩

private def extendPositive {n t : ℕ} (f : Config n t) (a : ↥(available f.1)) :
    Config (n + 1) (t + 1) :=
  ⟨append f.1 (positiveEntry a), by
    constructor
    · rw [card_active_append, if_neg (positiveEntry_ne_zero a), f.2.1]
    · exact (distinct_append _ _).2 ⟨f.2.2, fun _ => ((mem_available f.1 a.val).1 a.2).2⟩⟩

private noncomputable def stepEquiv (n t : ℕ) :
    (Config n (t + 1) ⊕ (Σ f : Config n t, ↥(available f.1))) ≃ Config (n + 1) (t + 1) := by
  classical
  let extend : (Config n (t + 1) ⊕ (Σ f : Config n t, ↥(available f.1))) →
      Config (n + 1) (t + 1) :=
    Sum.elim extendZero (fun s => extendPositive s.1 s.2)
  refine Equiv.ofBijective extend ⟨?_, ?_⟩
  · intro x y h
    rcases x with f | ⟨f, a⟩ <;> rcases y with g | ⟨g, b⟩
    · have he : append f.1 0 = append g.1 0 := congrArg Subtype.val h
      exact congrArg Sum.inl (Subtype.ext (append_eq_iff.mp he).1)
    · have he : append f.1 0 = append g.1 (positiveEntry b) := congrArg Subtype.val h
      have hz := congrArg Fin.val (append_eq_iff.mp he).2
      exact (positiveEntry_ne_zero b hz.symm).elim
    · have he : append f.1 (positiveEntry a) = append g.1 0 := congrArg Subtype.val h
      have hz := congrArg Fin.val (append_eq_iff.mp he).2
      exact (positiveEntry_ne_zero a hz).elim
    · have he : append f.1 (positiveEntry a) = append g.1 (positiveEntry b) :=
        congrArg Subtype.val h
      have hf : f = g := Subtype.ext (append_eq_iff.mp he).1
      subst g
      have hab : a = b := Subtype.ext (congrArg Fin.val (append_eq_iff.mp he).2)
      subst b
      rfl
  · intro g
    let f : Exponents n := fun i => g.1 i.castSucc
    let a : Fin (n + 1) := g.1 (Fin.last n)
    have he : append f a = g.1 := Fin.snoc_init_self g.1
    have hc : distinct (append f a) := by
      rw [he]
      exact g.2.2
    have hd := (distinct_append f a).1 hc
    have hcard : (active (append f a)).card = t + 1 := by
      rw [he]
      exact g.2.1
    rw [card_active_append] at hcard
    by_cases ha : a.val = 0
    · rw [if_pos ha, Nat.add_zero] at hcard
      let g₀ : Config n (t + 1) := ⟨f, hcard, hd.1⟩
      have hz : (0 : Fin (n + 1)) = a := Fin.ext ha.symm
      refine ⟨Sum.inl g₀, Subtype.ext ?_⟩
      change append f 0 = g.1
      rw [hz, he]
    · rw [if_neg ha] at hcard
      let g₀ : Config n t := ⟨f, by omega, hd.1⟩
      have hbound : a.val ≤ n := Nat.le_of_lt_succ a.isLt
      let b : ↥(available g₀.1) :=
        ⟨a.val, (mem_available f a.val).2 ⟨⟨Nat.pos_of_ne_zero ha, hbound⟩, hd.2 ha⟩⟩
      have hb : positiveEntry b = a := Fin.ext rfl
      refine ⟨Sum.inr ⟨g₀, b⟩, Subtype.ext ?_⟩
      change append f (positiveEntry b) = g.1
      rw [hb, he]

private theorem config_step (n t : ℕ) :
    Fintype.card (Config (n + 1) (t + 1)) =
      Fintype.card (Config n (t + 1)) + (n - t) * Fintype.card (Config n t) := by
  classical
  rw [Fintype.card_congr (stepEquiv n t).symm, Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_coe, card_available, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

private theorem config_zero (n : ℕ) : Fintype.card (Config n 0) = 1 := by
  classical
  let f : Exponents n := fun _ => 0
  have hf (i : Fin n) : exponent f i = 0 := rfl
  have hactive : active f = ∅ := by
    ext i
    simp [mem_active, hf]
  let inhabitant : Config n 0 :=
    ⟨f, by simp [hactive], distinct_iff.mpr (fun i _ hi _ _ => (hi (hf i)).elim)⟩
  let : Unique (Config n 0) := {
    default := inhabitant
    uniq := fun g => Subtype.ext (by
      funext i
      have he : active g.1 = ∅ := Finset.card_eq_zero.mp g.2.1
      apply Fin.ext
      change exponent g.1 i = exponent f i
      rw [hf]
      by_contra hn
      have hm := (mem_active g.1 i).2 hn
      rw [he] at hm
      exact Finset.notMem_empty i hm)
  }
  exact Fintype.card_unique

private theorem config_empty {n t : ℕ} (h : n < t) : Fintype.card (Config n t) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun f => ?_⟩
  have hb : (active f.1).card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ (active f.1)))
  exact (not_le_of_gt h) (f.2.1 ▸ hb)

private theorem local_stirling (n k : ℕ) : stirling2 n k = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [stirling2, Nat.stirlingSecond_succ_succ, ih]

private theorem config_count (n t : ℕ) (ht : t ≤ n) :
    Fintype.card (Config n t) = stirling2 n (n - t) := by
  induction n generalizing t with
  | zero =>
    have hz : t = 0 := by omega
    subst t
    rw [config_zero]
    rfl
  | succ n ih =>
    cases t with
    | zero =>
      rw [config_zero, Nat.sub_zero, local_stirling, Nat.stirlingSecond_self]
    | succ t =>
      rw [config_step]
      by_cases h : t < n
      · have he : n + 1 - (t + 1) = (n - (t + 1)) + 1 := by omega
        have hm : n - t = (n - (t + 1)) + 1 := by omega
        rw [ih (t + 1) (by omega), ih t (by omega), he, stirling2, ← hm, Nat.add_comm]
      · have ht' : t = n := by omega
        subst t
        rw [config_empty (Nat.lt_succ_self n), Nat.sub_self, Nat.zero_mul, Nat.add_zero,
          Nat.sub_self]
        rfl

-- Index the primes in reverse order so that coordinate i has exponent bound i.
-- The last prime in the usual ordering has bound zero and contributes no factor.
private noncomputable def primeAt {m : ℕ} (i : Fin (m + 1)) : ℕ :=
  Nat.nth Nat.Prime (m - i.val)

private theorem primeAt_prime {m : ℕ} (i : Fin (m + 1)) : Nat.Prime (primeAt i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

private theorem primeAt_injective {m : ℕ} :
    Function.Injective (primeAt : Fin (m + 1) → ℕ) := by
  intro i j h
  have hr : m - i.val = m - j.val :=
    Nat.nth_injective Nat.infinite_setOfPred_prime h
  have hi := i.isLt
  have hj := j.isLt
  exact Fin.ext (by omega)

private noncomputable def primeProduct (m : ℕ) (e : Fin (m + 1) → ℕ) : ℕ :=
  ∏ i, primeAt i ^ e i

private theorem primeProduct_ne_zero (m : ℕ) (e : Fin (m + 1) → ℕ) :
    primeProduct m e ≠ 0 := by
  unfold primeProduct
  exact Finset.prod_ne_zero_iff.2 (fun i _ => pow_ne_zero _ (primeAt_prime i).ne_zero)

private theorem superprimorial_eq_product (m : ℕ) :
    superprimorial m = primeProduct m Fin.val := by
  classical
  unfold superprimorial primeProduct
  have hinterval : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hmnot : m + 1 ∉ Finset.Icc 1 m := by
    intro h
    have hh := (Finset.mem_Icc.mp h).2
    omega
  calc
    (∏ i ∈ Finset.Icc 1 m, Nat.nth Nat.Prime (i - 1) ^ (m + 1 - i)) =
        ∏ i ∈ Finset.Icc 1 (m + 1), Nat.nth Nat.Prime (i - 1) ^ (m + 1 - i) := by
          rw [hinterval, Finset.prod_insert hmnot, Nat.sub_self, pow_zero, one_mul]
    _ = ∏ i : Fin (m + 1), primeAt i ^ i.val := by
      refine Finset.prod_bij
        (fun i hi => (⟨m + 1 - i, by
          have hl := (Finset.mem_Icc.mp hi).1
          omega⟩ : Fin (m + 1))) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj h
        have hi' := Finset.mem_Icc.mp hi
        have hj' := Finset.mem_Icc.mp hj
        have hv := congrArg Fin.val h
        change m + 1 - i = m + 1 - j at hv
        omega
      · intro j _
        have hj := j.isLt
        refine ⟨m + 1 - j.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        apply Fin.ext
        change m + 1 - (m + 1 - j.val) = j.val
        omega
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        have he : m - (m + 1 - i) = i - 1 := by omega
        change Nat.nth Nat.Prime (i - 1) ^ (m + 1 - i) =
          Nat.nth Nat.Prime (m - (m + 1 - i)) ^ (m + 1 - i)
        rw [he]

private theorem factorization_primeProduct (m : ℕ) (e : Fin (m + 1) → ℕ) (p : ℕ) :
    (primeProduct m e).factorization p =
      ∑ i : Fin (m + 1), if p = primeAt i then e i else 0 := by
  unfold primeProduct
  rw [Nat.factorization_prod_apply (fun i _ => pow_ne_zero (e i) (primeAt_prime i).ne_zero)]
  apply Finset.sum_congr rfl
  intro i _
  rw [(primeAt_prime i).factorization_pow]
  by_cases hp : p = primeAt i
  · rw [hp, if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg hp, Finsupp.single_eq_of_ne hp]

private theorem factorization_product_at {m : ℕ} (e : Fin (m + 1) → ℕ) (i : Fin (m + 1)) :
    (primeProduct m e).factorization (primeAt i) = e i := by
  rw [factorization_primeProduct, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [if_pos rfl]
  · intro j _ hji
    exact if_neg (fun he => hji (primeAt_injective he.symm))

private theorem factorization_product_outside {m : ℕ} (e : Fin (m + 1) → ℕ) (p : ℕ)
    (hp : ∀ i : Fin (m + 1), p ≠ primeAt i) :
    (primeProduct m e).factorization p = 0 := by
  simp only [factorization_primeProduct, hp, if_false, Finset.sum_const_zero]

private theorem good_iff_exponents {m t d : ℕ} {f : Exponents (m + 1)}
    (hat : ∀ i, d.factorization (primeAt i) = exponent f i)
    (hout : ∀ p, (∀ i : Fin (m + 1), p ≠ primeAt i) → d.factorization p = 0) :
    Good t d ↔ (active f).card = t ∧ distinct f := by
  classical
  have hmem (p : ℕ) : p ∈ d.primeFactors ↔ d.factorization p ≠ 0 := by
    simpa only [Nat.support_factorization] using
      (Finsupp.mem_support_iff (f := d.factorization) (a := p))
  have hmemAt (i : Fin (m + 1)) : primeAt i ∈ d.primeFactors ↔ exponent f i ≠ 0 := by
    rw [hmem, hat]
  have himage : d.primeFactors = (active f).image primeAt := by
    ext p
    rw [Finset.mem_image]
    constructor
    · intro hp
      have hex : ∃ i : Fin (m + 1), primeAt i = p := by
        by_contra h
        exact (hmem p).1 hp (hout p (fun i he => h ⟨i, he.symm⟩))
      obtain ⟨i, rfl⟩ := hex
      exact ⟨i, (mem_active f i).2 ((hmemAt i).1 hp), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hmemAt i).2 ((mem_active f i).1 hi)
  have hc : d.primeFactors.card = (active f).card := by
    rw [himage, Finset.card_image_of_injective _ primeAt_injective]
  unfold Good
  rw [hc, distinct_iff]
  constructor
  · rintro ⟨hcard, hd⟩
    refine ⟨hcard, ?_⟩
    intro i j hi hj he
    apply primeAt_injective
    apply hd ((hmemAt i).2 hi) ((hmemAt j).2 hj)
    rw [hat, hat, he]
  · rintro ⟨hcard, hf⟩
    refine ⟨hcard, ?_⟩
    intro p hp q hq he
    change p ∈ d.primeFactors at hp
    change q ∈ d.primeFactors at hq
    rw [himage, Finset.mem_image] at hp hq
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨j, hj, rfl⟩ := hq
    rw [hat, hat] at he
    exact congrArg primeAt (hf i j ((mem_active f i).1 hi) ((mem_active f j).1 hj) he)

private def Divisors (m t : ℕ) := {d : ℕ // d ∣ superprimorial m ∧ Good t d}

private noncomputable def divisorOfConfig {m t : ℕ} (f : Config (m + 1) t) :
    Divisors m t := by
  let d := primeProduct m (exponent f.1)
  have hd : d ≠ 0 := primeProduct_ne_zero _ _
  have hs : superprimorial m ≠ 0 := by
    rw [superprimorial_eq_product]
    exact primeProduct_ne_zero _ _
  refine ⟨d, (Nat.factorization_le_iff_dvd hd hs).1 ?_, ?_⟩
  · intro p
    rw [superprimorial_eq_product]
    by_cases hp : ∃ i : Fin (m + 1), p = primeAt i
    · obtain ⟨i, rfl⟩ := hp
      change (primeProduct m (exponent f.1)).factorization (primeAt i) ≤
        (primeProduct m Fin.val).factorization (primeAt i)
      rw [factorization_product_at, factorization_product_at]
      exact Nat.le_of_lt_succ (f.1 i).isLt
    · have hout (i : Fin (m + 1)) : p ≠ primeAt i := fun he => hp ⟨i, he⟩
      change (primeProduct m (exponent f.1)).factorization p ≤ _
      rw [factorization_product_outside _ _ hout]
      exact Nat.zero_le _
  · exact (good_iff_exponents (factorization_product_at (exponent f.1))
      (factorization_product_outside (exponent f.1))).2 f.2

private noncomputable def exponentEquiv (m t : ℕ) : Config (m + 1) t ≃ Divisors m t := by
  classical
  refine Equiv.ofBijective divisorOfConfig ⟨?_, ?_⟩
  · intro f g h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he := congrArg (fun d : Divisors m t => d.1.factorization (primeAt i)) h
    change (primeProduct m (exponent f.1)).factorization (primeAt i) =
      (primeProduct m (exponent g.1)).factorization (primeAt i) at he
    rw [factorization_product_at, factorization_product_at] at he
    exact he
  · intro d
    have hs : superprimorial m ≠ 0 := by
      rw [superprimorial_eq_product]
      exact primeProduct_ne_zero _ _
    have hd : d.1 ≠ 0 := ne_zero_of_dvd_ne_zero hs d.2.1
    have hle := (Nat.factorization_le_iff_dvd hd hs).2 d.2.1
    have hbound (i : Fin (m + 1)) : d.1.factorization (primeAt i) ≤ i.val := by
      calc
        d.1.factorization (primeAt i) ≤ (superprimorial m).factorization (primeAt i) :=
          hle (primeAt i)
        _ = i.val := by rw [superprimorial_eq_product, factorization_product_at]
    let f : Exponents (m + 1) :=
      fun i => ⟨d.1.factorization (primeAt i), Nat.lt_succ_of_le (hbound i)⟩
    have hat (i : Fin (m + 1)) : d.1.factorization (primeAt i) = exponent f i := rfl
    have hout (p : ℕ) (hp : ∀ i : Fin (m + 1), p ≠ primeAt i) :
        d.1.factorization p = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        d.1.factorization p ≤ (superprimorial m).factorization p := hle p
        _ = 0 := by rw [superprimorial_eq_product, factorization_product_outside _ _ hp]
    let g : Config (m + 1) t := ⟨f, (good_iff_exponents hat hout).1 d.2.2⟩
    refine ⟨g, Subtype.ext ?_⟩
    change primeProduct m (exponent f) = d.1
    apply Nat.eq_of_factorization_eq (primeProduct_ne_zero _ _) hd
    intro p
    by_cases hp : ∃ i : Fin (m + 1), p = primeAt i
    · obtain ⟨i, rfl⟩ := hp
      rw [factorization_product_at, hat i]
    · have hp' (i : Fin (m + 1)) : p ≠ primeAt i := fun he => hp ⟨i, he⟩
      rw [factorization_product_outside _ _ hp', hout p hp']

end OMA.S_oeis_a008278

open OMA.S_oeis_a008278

theorem OMA.solution : type_of% @OMA.S_oeis_a008278.main := by
  intro n k hk hkn
  cases n with
  | zero => omega
  | succ m =>
    change Nat.card (Divisors m (k - 1)) = stirling2 (m + 1) (m + 1 - k + 1)
    have he : m + 1 - (k - 1) = m + 1 - k + 1 := by omega
    rw [← Nat.card_congr (exponentEquiv m (k - 1)), Nat.card_eq_fintype_card,
      config_count _ _ (by omega), he]
