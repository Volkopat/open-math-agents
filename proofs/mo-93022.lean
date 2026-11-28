import OMAStatements.S_mo_93022
import Mathlib

/-!
A five-state automaton using two permutation letters. Every word of length at most four
preserves a nonconstant two-colouring, while the given word of length six is a five-cycle.
This retains the original counterexample's two permutations and omits its unused reset letter.
-/

namespace FiveStateAutomaton

open OMA.S_mo_93022

def transition (letter : Fin 2) : Fin 5 → Fin 5 :=
  if letter = 0 then ![3, 4, 2, 0, 1]
  else ![4, 2, 1, 0, 3]

def longWord : List (Fin 2) := [0, 1, 0, 1, 1, 1]

def words : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | n + 1 => [] :: ((words n).map (List.cons 0) ++ (words n).map (List.cons 1))

lemma mem_words {v : List (Fin 2)} {n : ℕ} (h : v.length ≤ n) : v ∈ words n := by
  induction n generalizing v with
  | zero =>
    have : v = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, words]
  | succ n ih =>
    cases v with
    | nil => simp [words]
    | cons b v =>
      have hv : v ∈ words n := ih (by simpa using h)
      fin_cases b <;> simp [words, hv]

lemma strongly_connected : Strong transition := by
  have paths : ∀ p q : Fin 5, ∃ v ∈ words 4, run transition v p = q := by decide
  intro p q
  obtain ⟨v, _, hv⟩ := paths p q
  exact ⟨v, hv⟩

lemma long_connects : Connecting (run transition longWord) := by
  have cycle : ∀ p q : Fin 5, p ≠ q → ∃ k : Fin 5,
      0 < k.val ∧ (run transition longWord)^[k.val] p = q := by decide
  intro p q hpq
  obtain ⟨k, hk, he⟩ := cycle p q hpq
  exact ⟨k.val, hk, Or.inl he⟩

set_option maxRecDepth 6000 in
lemma short_disconnected (v : List (Fin 2)) (hv : v.length ≤ 4) :
    ¬ Connecting (run transition v) := by
  have cuts : ∀ w ∈ words 4, ∃ tag : Fin 5 → Bool,
      (∀ i, tag (run transition w i) = tag i) ∧ ∃ p q, tag p ≠ tag q := by decide
  obtain ⟨tag, hinv, p, q, hdif⟩ := cuts v (mem_words hv)
  have keep (k : ℕ) (s : Fin 5) : tag ((run transition v)^[k] s) = tag s := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hinv, ih]
  intro hc
  obtain ⟨k, _, h | h⟩ := hc p q (fun he => hdif (congrArg tag he))
  · exact hdif ((keep k p).symm.trans (congrArg tag h))
  · exact hdif ((congrArg tag h).symm.trans (keep k q))

end FiveStateAutomaton

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_93022.main) := by
  intro h
  obtain ⟨v, hv, hc⟩ := h 5 2 (by decide) FiveStateAutomaton.transition
    FiveStateAutomaton.strongly_connected ⟨_, FiveStateAutomaton.long_connects⟩
  exact FiveStateAutomaton.short_disconnected v hv hc
