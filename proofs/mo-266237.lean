import OMAStatements.S_mo_266237
import Mathlib.Data.Fintype.BigOperators

/-!
# Random Balanced Assignment

Source: Steve, “Random Balanced Assignment” (2017),
https://mathoverflow.net/questions/266237.
Formal statement credit: @LDJAI.
Proof credit: @grp06.
-/

section

open Finset OMA.S_mo_266237
open scoped BigOperators Nat

/-- The fiber of the first projection of a dependent sum is its corresponding summand. -/
private noncomputable def summandFiber {K : ℕ} (h : Fin K → ℕ) (j : Fin K) :
    Fin (h j) ≃ {y : (Σ i, Fin (h i)) // y.1 = j} :=
  Equiv.ofBijective (fun k => ⟨⟨j, k⟩, rfl⟩) (by
    constructor
    · intro a b hab
      have hh : (⟨j, a⟩ : Σ i, Fin (h i)) = ⟨j, b⟩ := congrArg Subtype.val hab
      exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    · rintro ⟨⟨i, k⟩, hi⟩
      change i = j at hi
      subst i
      exact ⟨k, rfl⟩)

/-- A map of the specified profile, together with a labeling of every fiber,
is a bijection onto the dependent sum of the label sets. -/
private noncomputable def labeledMapsEquiv {A : Type*} [Fintype A] {K : ℕ}
    (h : Fin K → ℕ) :
    (Σ f : {f : A → Fin K // counts f = h},
      ∀ j, {x : A // f.1 x = j} ≃ Fin (h j)) ≃ (A ≃ Σ j, Fin (h j)) := by
  classical
  let encode (s : Σ f : {f : A → Fin K // counts f = h},
      ∀ j, {x : A // f.1 x = j} ≃ Fin (h j)) : A ≃ Σ j, Fin (h j) :=
    (Equiv.sigmaFiberEquiv s.1.1).symm.trans (Equiv.sigmaCongrRight s.2)
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · rintro ⟨⟨f, hf⟩, u⟩ ⟨⟨g, hg⟩, v⟩ huv
    have hfg : f = g := by
      funext x
      exact congrArg (fun e : A ≃ Σ j, Fin (h j) => (e x).1) huv
    subst g
    have he : u = v := by
      funext j
      apply Equiv.ext
      intro x
      obtain ⟨x, hx⟩ := x
      change f x = j at hx
      subst j
      have hh : (⟨f x, u (f x) ⟨x, rfl⟩⟩ : Σ j, Fin (h j)) =
          ⟨f x, v (f x) ⟨x, rfl⟩⟩ :=
        congrArg (fun e : A ≃ Σ j, Fin (h j) => e x) huv
      exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    cases he
    rfl
  · intro e
    let f : A → Fin K := fun x => (e x).1
    let restrict (j : Fin K) : {x : A // f x = j} ≃
        {y : (Σ i, Fin (h i)) // y.1 = j} :=
      e.subtypeEquivOfSubtype (p := fun y => y.1 = j)
    let label (j : Fin K) : {x : A // f x = j} ≃ Fin (h j) :=
      (restrict j).trans (summandFiber h j).symm
    have hf : counts f = h := by
      funext j
      calc
        counts f j = Fintype.card {x : A // f x = j} :=
          (Fintype.card_subtype (fun x : A => f x = j)).symm
        _ = Fintype.card (Fin (h j)) := Fintype.card_congr (label j)
        _ = h j := Fintype.card_fin _
    refine ⟨⟨⟨f, hf⟩, label⟩, ?_⟩
    apply Equiv.ext
    intro x
    have hh := (summandFiber h (f x)).apply_symm_apply (restrict (f x) ⟨x, rfl⟩)
    exact congrArg Subtype.val hh

private theorem card_maps_with_counts {A : Type*} [Fintype A] [DecidableEq A] {K : ℕ}
    (h : Fin K → ℕ) (hs : ∑ j, h j = Fintype.card A) :
    ((univ : Finset (A → Fin K)).filter (fun f => counts f = h)).card =
      Nat.multinomial univ h := by
  classical
  let S := (univ : Finset (A → Fin K)).filter (fun f => counts f = h)
  let forget : (↥S) ≃ {f : A → Fin K // counts f = h} :=
    Equiv.subtypeEquivRight (fun f => by simp [S])
  let : Fintype {f : A → Fin K // counts f = h} := Fintype.ofEquiv (↥S) forget
  have hbase : S.card = Fintype.card {f : A → Fin K // counts f = h} :=
    (Fintype.card_coe S).symm.trans (Fintype.card_congr forget)
  let e : A ≃ Σ j, Fin (h j) := Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hs.symm)
  have hfiber (f : {f : A → Fin K // counts f = h}) (j : Fin K) :
      Fintype.card ({x : A // f.1 x = j} ≃ Fin (h j)) = (h j)! := by
    have hc : Fintype.card {x : A // f.1 x = j} = h j :=
      (Fintype.card_subtype (fun x : A => f.1 x = j)).trans (congrFun f.2 j)
    let b : {x : A // f.1 x = j} ≃ Fin (h j) :=
      Fintype.equivOfCardEq (hc.trans (Fintype.card_fin _).symm)
    rw [Fintype.card_equiv b, hc]
  have hc : S.card * (∏ j, (h j)!) = (Fintype.card A)! := by
    calc
      S.card * (∏ j, (h j)!) =
          ∑ f : {f : A → Fin K // counts f = h}, ∏ j, (h j)! := by
            rw [Finset.sum_const, Nat.nsmul_eq_mul]
            exact congrArg (fun n : ℕ => n * (∏ j, (h j)!)) hbase
      _ = Fintype.card (Σ f : {f : A → Fin K // counts f = h},
            ∀ j, {x : A // f.1 x = j} ≃ Fin (h j)) := by
              simp only [Fintype.card_sigma, Fintype.card_pi, hfiber]
      _ = Fintype.card (A ≃ Σ j, Fin (h j)) :=
        Fintype.card_congr (labeledMapsEquiv h)
      _ = (Fintype.card A)! := Fintype.card_equiv e
  change S.card = Nat.multinomial univ h
  apply Nat.mul_right_cancel (Nat.prod_factorial_pos univ h)
  rw [hc]
  have hspec := Nat.multinomial_spec univ h
  rw [hs] at hspec
  exact hspec.symm.trans (Nat.mul_comm _ _)

private theorem card_partition {A : Type*} {B : Type*} [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) :
    s.card = ∑ j, (s.filter fun x => f x = j).card :=
  Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := univ) (fun {_} _ => mem_univ _)

private def profile {N K : ℕ} (τ f : Fin N → Fin K) (i j : Fin K) : ℕ :=
  (univ.filter fun x => τ x = i ∧ f x = j).card

private theorem profile_row {N K : ℕ} (τ f : Fin N → Fin K) (i : Fin K) :
    ∑ j, profile τ f i j = counts τ i := by
  simpa only [profile, counts, filter_filter] using
    (card_partition (univ.filter fun x => τ x = i) f).symm

private theorem profile_col {N K : ℕ} (τ f : Fin N → Fin K) (j : Fin K) :
    ∑ i, profile τ f i j = counts f j := by
  unfold counts
  rw [card_partition (univ.filter fun x => f x = j) τ]
  apply Finset.sum_congr rfl
  intro i _
  unfold profile
  apply congrArg Finset.card
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact and_comm

private theorem mem_balanced_iff {N K m : ℕ} (f : Fin N → Fin K) :
    f ∈ balanced N K m ↔ ∀ j, counts f j = m := by
  simp only [balanced, mem_filter, mem_univ, true_and]
  exact ⟨fun h j => congrFun h j, funext⟩

private theorem mem_tables_iff {K m : ℕ} (t : Fin K → Fin K → ℕ) :
    t ∈ tables K m ↔ (∀ i, ∑ j, t i j = m) ∧ (∀ j, ∑ i, t i j = m) := by
  simp [tables, Fintype.mem_piFinset]

private def rowMap {N K : ℕ} (τ f : Fin N → Fin K) (i : Fin K) :
    {x : Fin N // τ x = i} → Fin K :=
  fun x => f x.1

private theorem rowMap_counts {N K : ℕ} (τ f : Fin N → Fin K) (i j : Fin K) :
    counts (rowMap τ f i) j = profile τ f i j := by
  classical
  let e : {x : {x : Fin N // τ x = i} // rowMap τ f i x = j} ≃
      {x : Fin N // τ x = i ∧ f x = j} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := by rintro ⟨⟨x, hi⟩, hj⟩; rfl
      right_inv := by rintro ⟨x, hi, hj⟩; rfl }
  calc
    counts (rowMap τ f i) j =
        Fintype.card {x : {x : Fin N // τ x = i} // rowMap τ f i x = j} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {x : Fin N // τ x = i ∧ f x = j} := Fintype.card_congr e
    _ = profile τ f i j := Fintype.card_subtype _

private theorem card_profile {N K m : ℕ} {τ : Fin N → Fin K}
    (hτ : τ ∈ balanced N K m) (t : Fin K → Fin K → ℕ) (ht : t ∈ tables K m) :
    ((univ : Finset (Fin N → Fin K)).filter (fun f => profile τ f = t)).card =
      weight t := by
  classical
  let rows (i : Fin K) : Finset ({x : Fin N // τ x = i} → Fin K) :=
    univ.filter fun g => counts g = t i
  have hb (f : Fin N → Fin K) :
      profile τ f = t ↔ ∀ i, rowMap τ f i ∈ rows i := by
    simp only [rows, mem_filter, mem_univ, true_and]
    constructor
    · intro h i
      funext j
      exact (rowMap_counts τ f i j).trans (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (rowMap_counts τ f i j).symm.trans (congrFun (h i) j)
  calc
    _ = (Fintype.piFinset rows).card := by
      apply Finset.card_bij (fun f _ => rowMap τ f)
      · intro f hf
        exact Fintype.mem_piFinset.mpr ((hb f).mp (mem_filter.mp hf).2)
      · intro f _ g _ h
        funext x
        exact congrFun (congrFun h (τ x)) ⟨x, rfl⟩
      · intro g hg
        let f : Fin N → Fin K := fun x => g (τ x) ⟨x, rfl⟩
        have he : rowMap τ f = g := by
          funext i x
          obtain ⟨x, hx⟩ := x
          change τ x = i at hx
          subst i
          rfl
        refine ⟨f, mem_filter.mpr ⟨mem_univ _, (hb f).mpr ?_⟩, he⟩
        rw [he]
        exact Fintype.mem_piFinset.mp hg
    _ = ∏ i, (rows i).card := Fintype.card_piFinset rows
    _ = weight t := by
      unfold weight
      apply Finset.prod_congr rfl
      intro i _
      apply card_maps_with_counts
      calc
        ∑ j, t i j = m := ((mem_tables_iff t).mp ht).1 i
        _ = counts τ i := ((mem_balanced_iff τ).mp hτ i).symm
        _ = Fintype.card {x : Fin N // τ x = i} := (Fintype.card_subtype _).symm

private theorem profile_mismatch {N K : ℕ} (τ f : Fin N → Fin K)
    (p : Equiv.Perm (Fin K)) :
    (univ.filter fun x => f x ≠ p (τ x)).card =
      ∑ i, ∑ j, if j = p i then 0 else profile τ f i j := by
  let s : Finset (Fin N) := univ.filter fun x => f x ≠ p (τ x)
  change s.card = _
  rw [card_partition s τ]
  apply Finset.sum_congr rfl
  intro i _
  rw [card_partition (s.filter fun x => τ x = i) f]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = p i
  · rw [if_pos hj]
    have hempty : ((s.filter fun x => τ x = i).filter fun x => f x = j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxi := (mem_filter.mp (mem_filter.mp hx).1).2
      have hxj := (mem_filter.mp hx).2
      have hne := (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).2
      exact hne (by rw [hxi, hxj, hj])
    rw [hempty, card_empty]
  · rw [if_neg hj]
    unfold profile
    apply congrArg Finset.card
    ext x
    simp only [s, mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨by simpa only [h.1, h.2] using hj,
      h.1⟩, h.2⟩⟩

private theorem distance_profile {N K : ℕ} (τ f : Fin N → Fin K) :
    distance f τ = tableDistance (profile τ f) := by
  unfold distance tableDistance
  exact congrArg (fun g : Equiv.Perm (Fin K) → ℕ => univ.inf' univ_nonempty g)
    (funext (profile_mismatch τ f))

theorem OMA.solution : type_of% @OMA.S_mo_266237.main := by
  classical
  intro N K m _ hN τ hτ d
  have hden : (balanced N K m).card = Nat.multinomial univ (fun _ : Fin K => m) := by
    unfold balanced
    apply card_maps_with_counts
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      using hN.symm
  let assignments := (balanced N K m).filter fun f => distance f τ = d
  let outcomes := (tables K m).filter fun t => tableDistance t = d
  have hmaps : ∀ f ∈ assignments, profile τ f ∈ outcomes := by
    intro f hf
    have hfb := (mem_filter.mp hf).1
    have hfd := (mem_filter.mp hf).2
    apply mem_filter.mpr
    refine ⟨(mem_tables_iff _).mpr ⟨?_, ?_⟩, (distance_profile τ f).symm.trans hfd⟩
    · intro i
      exact (profile_row τ f i).trans ((mem_balanced_iff τ).mp hτ i)
    · intro j
      exact (profile_col τ f j).trans ((mem_balanced_iff f).mp hfb j)
  have hnum : assignments.card = ∑ t ∈ outcomes, weight t := by
    rw [Finset.card_eq_sum_card_fiberwise (f := profile τ) (s := assignments)
      (t := outcomes) (fun {f} hf => hmaps f hf)]
    apply Finset.sum_congr rfl
    intro t ht
    have htt := (mem_filter.mp ht).1
    have htd := (mem_filter.mp ht).2
    have heq : (assignments.filter fun f => profile τ f = t) =
        univ.filter (fun f => profile τ f = t) := by
      ext f
      simp only [assignments, mem_filter, mem_univ, true_and]
      refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
      · apply (mem_balanced_iff f).mpr
        intro j
        rw [← profile_col τ f j, h]
        exact ((mem_tables_iff t).mp htt).2 j
      · rw [distance_profile τ f, h]
        exact htd
    rw [heq]
    exact card_profile hτ t htt
  change (assignments.card : ℚ) / ((balanced N K m).card : ℚ) =
    ((∑ t ∈ outcomes, weight t : ℕ) : ℚ) / (Nat.multinomial univ (fun _ : Fin K => m) : ℚ)
  rw [hden, hnum]

end
