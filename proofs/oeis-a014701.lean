import OMAStatements.S_oeis_a014701

namespace OMA.S_oeis_a014701

private theorem double_chain (l : List ℕ) (h : stepChain l) :
    stepChain (l.map (fun x => 2 * x)) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
    cases l with
    | nil => trivial
    | cons y l =>
      obtain ⟨hr, ht⟩ := h
      refine ⟨?_, ih ht⟩
      change 2 * y = 2 * x ∨ 2 * y = 2 * (2 * x)
      rcases hr with h | h <;> omega

private theorem half_chain (l : List ℕ) (x : ℕ) (h : stepChain (2 * x :: l)) :
    ∃ t : List ℕ, l = t.map (fun y => 2 * y) ∧ stepChain (x :: t) := by
  induction l generalizing x with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons y l ih =>
    obtain ⟨hr, ht⟩ := h
    have hy : ∃ z : ℕ, y = 2 * z ∧ (z = x ∨ z = 2 * x) := by
      rcases hr with h | h
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨2 * x, by omega, Or.inr rfl⟩
    obtain ⟨z, hz, hrel⟩ := hy
    subst y
    obtain ⟨t, he, hc⟩ := ih z ht
    exact ⟨z :: t, congrArg (List.cons (2 * z)) he, ⟨hrel, hc⟩⟩

private theorem prepend_ones (c : ℕ) {l : List ℕ} (h : validSteps l) :
    validSteps (List.replicate c 1 ++ l) := by
  have hprepend (t : List ℕ) (ht : validSteps t) : validSteps (1 :: t) := by
    cases t with
    | nil => exact ⟨rfl, trivial⟩
    | cons x t =>
      obtain ⟨rfl, hc⟩ := ht
      exact ⟨rfl, ⟨Or.inl rfl, hc⟩⟩
  induction c with
  | zero => exact h
  | succ c ih => exact hprepend _ ih

private theorem add_initial_ones {c : ℕ} (hc : 0 < c) {t : List ℕ} (ht : validSteps t) :
    validSteps (List.replicate c 1 ++ t.map (fun x => 2 * x)) := by
  have hbase : validSteps (1 :: t.map (fun x => 2 * x)) := by
    cases t with
    | nil => exact ⟨rfl, trivial⟩
    | cons x t =>
      obtain ⟨rfl, h⟩ := ht
      exact ⟨rfl, ⟨Or.inr rfl, double_chain (1 :: t) h⟩⟩
  obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simpa [List.replicate_add, List.append_assoc] using prepend_ones c hbase

private theorem split_steps (l : List ℕ) (hl : validSteps l) (hn : l ≠ []) :
    ∃ c t, 0 < c ∧ validSteps t ∧ l = List.replicate c 1 ++ t.map (fun x => 2 * x) := by
  induction l with
  | nil => exact (hn rfl).elim
  | cons x l ih =>
    obtain ⟨rfl, h⟩ := hl
    cases l with
    | nil => exact ⟨1, [], by decide, trivial, rfl⟩
    | cons y l =>
      obtain ⟨hy, ht⟩ := h
      rcases hy with rfl | htwo
      · obtain ⟨c, t, hc, hvalid, he⟩ := ih ⟨rfl, ht⟩ (by simp)
        exact ⟨c + 1, t, by omega, hvalid, congrArg (List.cons 1) he⟩
      · have hy2 : y = 2 := by omega
        subst y
        obtain ⟨t, he, hchain⟩ := half_chain l 1 ht
        exact ⟨1, 1 :: t, by decide, ⟨rfl, hchain⟩, congrArg (List.cons 1 ∘ List.cons 2) he⟩

private theorem double_sum (l : List ℕ) :
    (l.map (fun x => 2 * x)).sum = 2 * l.sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.mul_add]

private def firstSteps (n : ℕ) : ℕ := if n % 2 = 1 then 1 else 2

private def cost (n : ℕ) : ℕ := chandah (n + 1)

private theorem first_positive (n : ℕ) : 0 < firstSteps n := by
  unfold firstSteps
  split <;> decide

private theorem leading_count {n c l : ℕ} (hc : 0 < c) (hs : n = c + 2 * l) :
    c = firstSteps n + 2 * ((c - firstSteps n) / 2) := by
  unfold firstSteps
  split <;> omega

private theorem cost_step {n : ℕ} (hn : 0 < n) :
    cost n = firstSteps n + cost ((n - firstSteps n) / 2) := by
  unfold cost
  rw [chandah.eq_def (n + 1), if_neg (show ¬ n + 1 ≤ 1 by omega)]
  by_cases ho : n % 2 = 1
  · rw [if_pos (show (n + 1) % 2 = 0 by omega), firstSteps, if_pos ho]
    rw [show (n + 1) / 2 = (n - 1) / 2 + 1 by omega, Nat.add_comm]
  · rw [if_neg (show ¬ (n + 1) % 2 = 0 by omega), firstSteps, if_neg ho]
    rw [show (n + 1) / 2 = (n - 2) / 2 + 1 by omega, Nat.add_comm]

private theorem cost_spec (n : ℕ) :
    (∃ l : List ℕ, validSteps l ∧ l.sum = n ∧ l.length = cost n) ∧
    (∀ l : List ℕ, validSteps l → l.sum = n → cost n ≤ l.length) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hc : cost 0 = 0 := by simp [cost, chandah.eq_def]
      exact ⟨⟨[], trivial, rfl, hc.symm⟩, fun l _ _ => by rw [hc]; omega⟩
    · let c := firstSteps n
      let m := (n - c) / 2
      have hc : 0 < c := first_positive n
      have hnm : n = c + 2 * m := leading_count (show 0 < n by omega) (by omega : n = n + 2 * 0)
      have hm : m < n := by omega
      have hcost : cost n = c + cost m := cost_step (by omega)
      obtain ⟨⟨t, ht, hsum, hlen⟩, hmin⟩ := ih m hm
      constructor
      · refine ⟨List.replicate c 1 ++ t.map (fun x => 2 * x), add_initial_ones hc ht, ?_, ?_⟩
        · simp [List.sum_replicate, double_sum, hsum, ← hnm]
        · simp [hlen, hcost]
      · intro l hl hs
        have hne : l ≠ [] := by
          rintro rfl
          exact hn hs.symm
        obtain ⟨d, q, hd, hq, hlq⟩ := split_steps l hl hne
        have hsumq : d + 2 * q.sum = n := by
          simpa [hlq, List.sum_replicate, double_sum] using hs
        let e := (d - c) / 2
        have hde : d = c + 2 * e := leading_count hd hsumq.symm
        have hqs : (List.replicate e 1 ++ q).sum = m := by
          simp [List.sum_replicate]
          omega
        have hb := hmin _ (prepend_ones e hq) hqs
        simp only [List.length_append, List.length_replicate] at hb
        rw [hcost, hlq, List.length_append, List.length_replicate, List.length_map]
        omega

end OMA.S_oeis_a014701

open OMA.S_oeis_a014701 in
theorem OMA.solution : type_of% @OMA.S_oeis_a014701.main := by
  intro n
  obtain ⟨⟨l, hl, hs, hlen⟩, hmin⟩ := cost_spec n
  exact ⟨⟨l, hl, hs, hlen⟩, fun _ ⟨t, ht, hts, htl⟩ => htl ▸ hmin t ht hts⟩
