import OMAStatements.S_erdos_811
import Mathlib

/-!
Reduction erdos-811.R1: Erdős Problem 811 (the rainbow `C_6` challenge) split by `n` modulo 12.

A balanced six-colouring of `K_n` gives every vertex exactly `n / 6` neighbours of each colour.
With `n = 6q + 1` the colour class of one colour is a `q`-regular graph on `6q + 1` vertices, so
by the handshake lemma it has `q (6q + 1) / 2` edges, which is not an integer when `q` is odd.
Hence no balanced colouring exists at all when `n` is `7` modulo `12` (then `q` is odd), and the
challenge only concerns `n` congruent to `1` modulo `12`.

H1 is that parity obstruction: a counting statement, independent of the rest of the problem.
H2 is the challenge itself restricted to `n` congruent to `1` modulo `12`; it is the open part.
-/

namespace OMA.R_erdos_811_R1

open OMA.S_erdos_811 (Balanced RainbowC6)

/-- Parity obstruction: for `n = 7 (mod 12)` there is no balanced edge-colouring of `K_n` with six
colours, because the colour class of any fixed colour would be an odd-regular graph on an odd
number of vertices. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 12 = 7 → ∀ c : Sym2 (Fin n) → Fin 6, ¬ Balanced c

/-- The open content of Erdős Problem 811: the rainbow `C_6` challenge in the only degrees where a
balanced colouring can exist, `n = 1 (mod 12)`. -/
def H2 : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n % 12 = 1 → ∀ c : Sym2 (Fin n) → Fin 6,
    Balanced c → ∃ f : Fin 6 → Fin n, RainbowC6 c f

theorem main : H1 → H2 → type_of% @OMA.S_erdos_811.main := by
  rintro h1 ⟨N₀, h2⟩
  refine ⟨N₀, fun n hn h6 c hc => ?_⟩
  have hlt : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hmod : (n % 12) % 6 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by norm_num : (6 : ℕ) ∣ 12)]
    exact h6
  have hres : n % 12 = 1 ∨ n % 12 = 7 := by omega
  rcases hres with h | h
  · exact h2 n hn h c hc
  · exact absurd hc (h1 n h c)

end OMA.R_erdos_811_R1
