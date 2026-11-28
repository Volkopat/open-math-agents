import OMAStatements.S_arxiv_2510_24280
import Mathlib

/-!
Disproof of Conjecture 4 of arXiv 2510.24280 as stated in `OMA.S_arxiv_2510_24280.main`.

Counterexample: `S = {3, 5, 12, 16, 30}`, heap `83`. With both players friendly the outcome is `(48, 35)`;
with both antagonistic it is `(47, 36)`. So the second player is strictly better off when both players are
antagonistic. (With friendly play the move `16` is worth `48` to the mover; with antagonistic play it is
worth only `46`, the mover takes `12` or `30` for `47`, and that leaves `36` to the other player.)

Proof: `tabF` and `tabA` list the outcomes for the heaps `0, ..., 83`. `tab_ok` checks, by kernel
evaluation, that each entry is obtained from the earlier entries by the recurrence `step`. Strong
induction (`bridge`) then identifies `outcome` with the table.
-/

namespace OMA.S_arxiv_2510_24280

/-- The subtraction set of the counterexample. -/
def S5 : Finset ℕ := {3, 5, 12, 16, 30}

/-- Outcomes with both players friendly, heaps `0, ..., 83`. -/
def tabF : List (ℕ × ℕ) :=
  [
    (0, 0), (0, 0), (0, 0), (3, 0), (3, 0), (5, 0), (5, 0), (5, 0), (5, 3), (5, 3), (5, 5), (6, 5),
    (12, 0), (12, 0), (12, 0), (12, 3), (16, 0), (16, 0), (16, 0), (16, 3), (16, 3), (16, 5),
    (17, 5), (17, 6), (19, 5), (19, 5), (21, 5), (21, 6), (16, 12), (16, 12), (30, 0), (30, 0),
    (30, 0), (30, 3), (30, 3), (30, 5), (30, 5), (30, 5), (33, 5), (33, 5), (35, 5), (35, 6),
    (30, 12), (30, 12), (30, 12), (33, 12), (30, 16), (30, 16), (30, 16), (33, 16), (33, 16),
    (35, 16), (35, 17), (36, 17), (35, 19), (35, 19), (35, 21), (36, 21), (42, 16), (42, 16),
    (30, 30), (30, 30), (32, 30), (33, 30), (33, 30), (35, 30), (35, 30), (35, 32), (35, 33),
    (35, 33), (35, 35), (36, 35), (42, 30), (42, 30), (42, 32), (42, 33), (46, 30), (46, 30),
    (46, 32), (46, 33), (46, 33), (46, 35), (47, 35), (48, 35)
  ]

/-- Outcomes with both players antagonistic, heaps `0, ..., 83`. -/
def tabA : List (ℕ × ℕ) :=
  [
    (0, 0), (0, 0), (0, 0), (3, 0), (3, 0), (5, 0), (5, 0), (5, 0), (5, 3), (5, 3), (5, 5), (6, 5),
    (12, 0), (12, 0), (12, 0), (12, 3), (16, 0), (16, 0), (16, 0), (16, 3), (16, 3), (16, 5),
    (17, 5), (17, 6), (19, 5), (19, 5), (21, 5), (21, 6), (16, 12), (16, 12), (30, 0), (30, 0),
    (30, 0), (30, 3), (30, 3), (30, 5), (30, 5), (30, 5), (33, 5), (33, 5), (35, 5), (35, 6),
    (30, 12), (30, 12), (30, 12), (33, 12), (30, 16), (30, 16), (30, 16), (33, 16), (33, 16),
    (35, 16), (35, 17), (36, 17), (35, 19), (35, 19), (35, 21), (36, 21), (42, 16), (42, 16),
    (30, 30), (30, 30), (32, 30), (33, 30), (33, 30), (35, 30), (35, 30), (35, 30), (35, 33),
    (35, 33), (35, 35), (36, 35), (42, 30), (42, 30), (42, 30), (42, 33), (46, 30), (46, 30),
    (46, 30), (46, 33), (46, 33), (46, 35), (47, 35), (47, 36)
  ]

def tab (c : Bool) (k : ℕ) : ℕ × ℕ := (if c then tabF else tabA).getD k (0, 0)

theorem outcome_eq (S : Finset ℕ) (c₁ c₂ : Bool) (h : ℕ) :
    outcome S c₁ c₂ h = step S c₁ h (fun k => if k < h then outcome S c₂ c₁ k else (0, 0)) := by
  rw [outcome]
  simp only [dite_eq_ite]

theorem tab_ok : ∀ c : Bool, ∀ h : Fin 84,
    tab c h = step S5 c h (fun k => if k < h then tab c k else (0, 0)) := by
  decide +kernel

theorem bridge (c : Bool) : ∀ h : ℕ, h < 84 → outcome S5 c c h = tab c h := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    have e : (fun k => if k < h then outcome S5 c c k else (0, 0)) =
        (fun k => if k < h then tab c k else (0, 0)) := by
      funext k
      by_cases hk : k < h
      · simp only [hk, if_true]
        exact ih k hk (by omega)
      · simp only [hk, if_false]
    rw [outcome_eq, e]
    exact (tab_ok c ⟨h, hh⟩).symm

end OMA.S_arxiv_2510_24280

open OMA.S_arxiv_2510_24280 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2510_24280.main) := by
  intro hm
  have h := (hm S5 (by decide) (by decide) 83).2
  rw [bridge false 83 (by norm_num), bridge true 83 (by norm_num)] at h
  exact absurd h (by decide)
