import Mathlib

/-!
# A uniform version of Van der Waerden's theorem

Source: https://mathoverflow.net/questions/485092
Credit: @ivillar

Status: false as stated; kept as the target of a disproof. The colouring of the natural numbers
by the Thue-Morse sequence (the parity of the binary digit sum) is a counterexample: for every
fixed difference `d ≥ 1` the monochromatic arithmetic progressions with difference `d` have
bounded length. This is the answer given in the comments (Thomas Bloom), and the question itself
says that the answer is negative.

Question. The following uniform version of Van der Waerden's theorem seems reasonable to me.
Is it true that for any partition of $\mathbb{N}=A_0 \sqcup A_1$, there is some $d$ so that
there is some $i\in \{0,1\}$ for which $A_i$ contains arbitrarily long arithmetic progressions
with fixed difference $d$? It can be shown the question has a positive answer for almost every
partition. However, it can be proved, by a dynamical system method shown by one of my
colleagues, that the question has a negative answer. Now I wonder whether this is a known
result? Or is there any further study along this line?

Formalization notes:
* A partition `ℕ = A₀ ⊔ A₁` is given by a set `A : Set ℕ` (`A₁ = A`, `A₀ = Aᶜ`).
* The common difference `d` is positive (for `d = 0` the statement would be trivial).
* `A_i` contains arbitrarily long arithmetic progressions with difference `d`: for every length
  `L` there is a starting point `a` with `a + k * d ∈ A_i` for all `k < L`.
* `main` states the positive answer to the (bolded) question; it is false.
* Not formalized: the follow-up questions (whether the negative answer is a known result, and
  whether there is further study along this line).
-/

namespace OMA.S_mo_485092

theorem main : ∀ A : Set ℕ, ∃ d : ℕ, 0 < d ∧
    ((∀ L : ℕ, ∃ a : ℕ, ∀ k : ℕ, k < L → a + k * d ∈ A) ∨
      (∀ L : ℕ, ∃ a : ℕ, ∀ k : ℕ, k < L → a + k * d ∉ A)) := by
  sorry

end OMA.S_mo_485092
