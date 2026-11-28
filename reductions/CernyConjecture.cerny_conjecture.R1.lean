import FormalConjectures.Wikipedia.CernyConjecture

-- Reduction of the Černý conjecture to its strongly connected hard-pair, higher-rank case.
-- Credit: @xsgxlz

namespace OMA.R_CernyConjecture_cerny_conjecture_R1

universe u v

/-- The remaining case has a strongly connected transition graph, a pair
that cannot merge in n letters, and no letter of rank at most two. -/
def H1 : Prop :=
  ∀ {α σ : Type} [Fintype σ] (M : DFA α σ), M.IsSynchronizing →
    (∀ x y, ∃ w : List α, M.evalFrom x w = y) →
    (¬ ∀ x y, ∃ w : List α, M.evalFrom x w = M.evalFrom y w ∧ w.length ≤ Fintype.card σ) →
    (¬ ∃ (a : α) (x y : σ), ∀ q, M.step q a = x ∨ M.step q a = y) →
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1)^2

/-- The short-pair case. -/
def H2 : Prop :=
  ∀ {α σ : Type} [Fintype σ] (M : DFA α σ),
    (∀ x y, ∃ w : List α, M.evalFrom x w = M.evalFrom y w ∧ w.length ≤ Fintype.card σ) →
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1)^2

/-- The rank-at-most-two letter case, including constant letters. -/
def H3 : Prop :=
  ∀ {α σ : Type} [Fintype σ] (M : DFA α σ), M.IsSynchronizing →
    (∃ (a : α) (x y : σ), ∀ q, M.step q a = x ∨ M.step q a = y) →
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1)^2

variable {α : Type u} {σ : Type v}

theorem short_entry [Fintype σ] (M : DFA α σ) (c : Finset σ) (x : σ)
    (can : ∃ w, M.evalFrom x w ∈ c) :
    ∃ w, M.evalFrom x w ∈ c ∧ w.length ≤ Fintype.card σ - c.card := by
  classical
  let P (k : Nat) := ∃ w : List α, w.length = k ∧ M.evalFrom x w ∈ c
  have ex : ∃ k, P k := by
    obtain ⟨w, hw⟩ := can
    exact ⟨_, w, rfl, hw⟩
  obtain ⟨w, hw, ends⟩ := Nat.find_spec ex
  have minimal (v : List α) (hv : M.evalFrom x v ∈ c) : w.length ≤ v.length := by
    rw [hw]
    exact Nat.find_min' ex ⟨v, rfl, hv⟩
  let state (i : Nat) := M.evalFrom x (w.take i)
  have outsideBefore (i : Nat) (hi : i < w.length) : state i ∉ c := by
    intro hm
    have hl := minimal _ hm
    change w.length ≤ (w.take i).length at hl
    simp only [List.length_take, Nat.min_eq_left hi.le] at hl
    omega
  have distinct (i j : Nat) (hij : i < j) (hj : j < w.length) (heq : state i = state j) :
      False := by
    have short : M.evalFrom x (w.take i ++ w.drop j) ∈ c := by
      rw [DFA.evalFrom_of_append, show M.evalFrom x (w.take i) = M.evalFrom x (w.take j) from heq,
        ← DFA.evalFrom_of_append, List.take_append_drop]
      exact ends
    have hl := minimal _ short
    simp only [List.length_append, List.length_take, Nat.min_eq_left (hij.trans hj).le,
      List.length_drop] at hl
    omega
  have count := Finset.card_le_card_of_injOn (s := Finset.range w.length)
    (t := Finset.univ \ c) state (fun i hi => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, outsideBefore i (Finset.mem_range.mp hi)⟩)
    (by
      intro i hi j hj heq
      rcases lt_trichotomy i j with h | h | h
      · exact (distinct i j h (Finset.mem_range.mp hj) heq).elim
      · exact h
      · exact (distinct j i h (Finset.mem_range.mp hi) heq.symm).elim)
  exact ⟨w, ends, by simpa [Finset.card_sdiff_of_subset (Finset.subset_univ c)] using count⟩

theorem enter_from_list (M : DFA α σ) (c : Finset σ) (k : Nat)
    (closed : ∀ x ∈ c, ∀ v, M.evalFrom x v ∈ c)
    (enter : ∀ x, ∃ v, M.evalFrom x v ∈ c ∧ v.length ≤ k)
    (xs : List σ) :
    ∃ w, (∀ x ∈ xs, M.evalFrom x w ∈ c) ∧ w.length ≤ xs.length * k := by
  cases xs with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons x tail =>
    obtain ⟨u, hx, hu⟩ := enter x
    obtain ⟨v, htail, hv⟩ := enter_from_list M c k closed enter
      (tail.map fun q => M.evalFrom q u)
    refine ⟨u ++ v, ?_, ?_⟩
    · intro q hq
      rw [DFA.evalFrom_of_append]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact closed _ hx v
      · exact htail _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    · simp only [List.length_map] at hv
      simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
termination_by xs.length
decreasing_by simp

theorem enter_closed_set [Fintype σ] (M : DFA α σ) (c : Finset σ)
    (closed : ∀ x ∈ c, ∀ v, M.evalFrom x v ∈ c)
    (enter : ∀ x, ∃ v, M.evalFrom x v ∈ c) :
    ∃ w, (∀ x, M.evalFrom x w ∈ c) ∧ w.length ≤ (Fintype.card σ - c.card)^2 := by
  classical
  obtain ⟨w, hw, hlen⟩ := enter_from_list M c _ closed (fun x => short_entry M c x (enter x))
    (Finset.univ \ c).toList
  refine ⟨w, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ c
    · exact closed x hx w
    · exact hw x (Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩))
  · simpa [Finset.card_sdiff_of_subset (Finset.subset_univ c), Nat.pow_two] using hlen

/-- Restrict to the positions of any known reset word, and enumerate the
states. This lets a result for small finite types cover all Lean universes
and arbitrary alphabets, with exactly the same length bound. -/
theorem of_finite_encodings [Fintype σ]
    (solve : ∀ {β τ : Type} [Fintype τ] (A : DFA β τ), A.IsSynchronizing →
      ∃ w : List β, A.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card τ - 1)^2)
    (M : DFA α σ) (sync : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1)^2 := by
  classical
  obtain ⟨r, z, reset⟩ := sync
  let e := Fintype.equivFin σ
  let letter (i : Fin r.length) := r[i.val]
  let B : DFA (Fin r.length) (Fin (Fintype.card σ)) := {
    step := fun x i => e (M.step (e.symm x) (letter i))
    start := e M.start
    accept := fun x => e.symm x ∈ M.accept }
  have transport (x : σ) (w : List (Fin r.length)) :
      e (M.evalFrom x (w.map letter)) = B.evalFrom (e x) w := by
    induction w generalizing x with
    | nil => rfl
    | cons i w ih =>
      simp only [List.map_cons, DFA.evalFrom_cons]
      simpa [B] using ih (M.step x (letter i))
  let indices : List (Fin r.length) := List.ofFn id
  have spell : indices.map letter = r := by
    simp [indices, letter, List.map_ofFn, Function.comp_def]
  have syncB : B.IsSynchronizing := by
    refine ⟨indices, e z, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← transport, spell, reset]
  obtain ⟨w, ⟨q, hq⟩, hlen⟩ := solve B syncB
  refine ⟨w.map letter, ⟨e.symm q, fun x => ?_⟩, by simpa using hlen⟩
  apply e.injective
  rw [transport, hq, e.apply_symm_apply]


theorem main : H1 → H2 → H3 → type_of% @CernyConjecture.cerny_conjecture := by
  intro hard shortPairs lowRank α σ inst M sync
  apply of_finite_encodings _ M sync
  intro α σ inst M sync
  classical
  obtain ⟨r, z, reset⟩ := sync
  let c := Finset.univ.filter fun x => ∃ v : List α, M.evalFrom z v = x
  have reach (x : σ) : x ∈ c ↔ ∃ v : List α, M.evalFrom z v = x := by simp [c]
  have hz : z ∈ c := (reach z).mpr ⟨[], rfl⟩
  have closed (x : σ) (hx : x ∈ c) (v : List α) : M.evalFrom x v ∈ c := by
    obtain ⟨u, hu⟩ := (reach x).mp hx
    exact (reach _).mpr ⟨u ++ v, by rw [DFA.evalFrom_of_append, hu]⟩
  obtain ⟨u, hu, ulen⟩ := enter_closed_set M c closed (fun x => ⟨r, by rw [reset x]; exact hz⟩)
  let A : DFA α c := {
    step := fun x a => ⟨M.step x a, closed x x.property [a]⟩
    start := ⟨z, hz⟩
    accept := fun x => x.val ∈ M.accept }
  have liftWord (x : c) (v : List α) : (A.evalFrom x v).val = M.evalFrom x.val v := by
    induction v generalizing x with
    | nil => rfl
    | cons a v ih => exact ih (A.step x a)
  have connected : ∀ x y, ∃ w : List α, A.evalFrom x w = y := by
    intro x y
    obtain ⟨v, hv⟩ := (reach y.val).mp y.property
    exact ⟨r ++ v, Subtype.ext (by rw [liftWord, DFA.evalFrom_of_append, reset, hv])⟩
  have syncA : A.IsSynchronizing := ⟨r, ⟨z, hz⟩, fun x => Subtype.ext ((liftWord x r).trans (reset x.val))⟩
  have bound : ∃ v, A.IsSynchronizingWord v ∧ v.length ≤ (Fintype.card c - 1)^2 := by
    by_cases hpairs : ∀ x y, ∃ w : List α, A.evalFrom x w = A.evalFrom y w ∧ w.length ≤ Fintype.card c
    · exact shortPairs A hpairs
    by_cases hrank : ∃ (a : α) (x y : c), ∀ q, A.step q a = x ∨ A.step q a = y
    · exact lowRank A syncA hrank
    exact hard A syncA connected hpairs hrank
  obtain ⟨v, ⟨y, hy⟩, vlen⟩ := bound
  refine ⟨u ++ v, ⟨y.val, fun x => ?_⟩, ?_⟩
  · rw [DFA.evalFrom_of_append]
    let x' : c := ⟨M.evalFrom x u, hu x⟩
    exact (liftWord x' v).symm.trans (congrArg Subtype.val (hy x'))
  · rw [List.length_append]
    apply (Nat.add_le_add ulen vlen).trans
    rw [Fintype.card_coe]
    have hc : c.card ≤ Fintype.card σ := Finset.card_le_univ c
    have hn : 1 ≤ c.card := Finset.one_le_card.mpr ⟨z, hz⟩
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hc
    have outsideCount : Fintype.card σ - c.card = b := by omega
    have coreCount : c.card - 1 = a := by omega
    have totalCount : Fintype.card σ - 1 = a + b := by omega
    rw [outsideCount, coreCount, totalCount]
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
    omega

end OMA.R_CernyConjecture_cerny_conjecture_R1
