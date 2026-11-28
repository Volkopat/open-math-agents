import OMAStatements.S_mo_247107

namespace UpDownProof
open Finset OMA.S_mo_247107
variable {n : ℕ}

/-- Finite set of words, used only to prove what the numerical recurrence counts. -/
def words : ℕ → Inventory n → (Fin n → Bool) → Bool → Finset (List (Fin n))
  | 0, r, _, _ => if ∀ j, r j = 0 then {[]} else ∅
  | k + 1, r, allowed, up =>
      (heads r allowed).biUnion fun i =>
        (words k (consume r i) (compareNext up i) (!up)).image (List.cons i)

private theorem consume_spec (r : Inventory n) (i : Fin n) (l : List (Fin n)) :
    (∀ j, (i :: l).count j = r j) ↔
      0 < r i ∧ ∀ j, l.count j = consume r i j := by
  constructor
  · intro h
    have hi := h i
    simp only [List.count_cons_self] at hi
    refine ⟨by omega, fun j => ?_⟩
    by_cases hj : j = i
    · subst j
      simp [consume, ← hi]
    · simpa [consume, hj, List.count_cons_of_ne (Ne.symm hj)] using h j
  · rintro ⟨hp, h⟩ j
    by_cases hj : j = i
    · subst j
      have hi := h i
      simp [consume] at hi
      simp only [List.count_cons_self]
      omega
    · simpa [consume, hj, List.count_cons_of_ne (Ne.symm hj)] using h j

theorem mem_words (k : ℕ) (r : Inventory n) (allowed : Fin n → Bool) (up : Bool)
    (w : List (Fin n)) :
    w ∈ words k r allowed up ↔
      w.length = k ∧ (∀ j, w.count j = r j) ∧ alternating allowed up w = true := by
  induction k generalizing r allowed up w with
  | zero =>
    cases w with
    | nil => by_cases h : ∀ j, r j = 0 <;> simp [words, alternating, h, eq_comm]
    | cons i l => by_cases h : ∀ j, r j = 0 <;> simp [words, h]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons i l =>
      simp only [words, mem_biUnion, mem_image, List.cons.injEq]
      constructor
      · rintro ⟨j, hj, tail, ht, rfl, rfl⟩
        obtain ⟨hp, ha⟩ := (mem_filter.mp hj).2
        obtain ⟨hl, hc, hs⟩ := (ih ..).mp ht
        exact ⟨by simp [hl], (consume_spec ..).mpr ⟨hp, hc⟩, by simp [alternating, ha, hs]⟩
      · rintro ⟨hlen, hcount, halt⟩
        obtain ⟨hp, hc⟩ := (consume_spec ..).mp hcount
        obtain ⟨ha, hs⟩ := Bool.and_eq_true_iff.mp halt
        exact ⟨i, mem_filter.mpr ⟨mem_univ _, hp, ha⟩, l,
          (ih ..).mpr ⟨by simpa using hlen, hc, hs⟩, rfl, rfl⟩

theorem card_words (k : ℕ) (r : Inventory n) (allowed : Fin n → Bool) (up : Bool) :
    (words k r allowed up).card = count k r allowed up := by
  induction k generalizing r allowed up with
  | zero => by_cases h : ∀ j, r j = 0 <;> simp [words, count, h]
  | succ k ih =>
    rw [words, count, card_biUnion]
    · apply sum_congr rfl
      intro i _
      rw [card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih]
    · intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro w hi hj
      obtain ⟨u, _, rfl⟩ := mem_image.mp hi
      obtain ⟨v, _, he⟩ := mem_image.mp hj
      exact hij (List.cons.inj he).1.symm

end UpDownProof

open UpDownProof

theorem OMA.solution : type_of% @OMA.S_mo_247107.main := by
  intro n
  exact ⟨_, fun _ => mem_words .., card_words ..⟩
