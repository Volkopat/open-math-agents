import FormalConjectures.OEIS.«234246»

/-!
Sun's conjecture that k phi(n - k) + 1 is a square for some 0 < k < n when n
does not divide 6. Classical slice from the identity
(c^2 f + 2c) f + 1 = (c f + 1)^2 and (c^2 f - 2c) f + 1 = (c f - 1)^2 with
f = phi(j): taking n - k = j shows a(n) > 0 for every n of the form
j + c^2 phi(j) + 2c or j + c^2 phi(j) - 2c (j, c at least 1, the second
when positive). This infinite family covers about 95 percent of n up to
20000; H2 is the remaining n (33, 41, 45, 53, 76, ...), still open.
-/

namespace OMA.R_OeisA234246_conjecture_1_R1

def H1 : Prop := ∀ j c : ℕ, 0 < j → 0 < c →
    0 < OeisA234246.a (j + (c ^ 2 * j.totient + 2 * c)) ∧
    (2 * c < c ^ 2 * j.totient → 0 < OeisA234246.a (j + (c ^ 2 * j.totient - 2 * c)))

def H2 : Prop := ∀ n : ℕ, 0 < n → ¬ n ∣ 6 →
    (∀ j c : ℕ, 0 < j → 0 < c → n ≠ j + (c ^ 2 * j.totient + 2 * c) ∧
      (2 * c < c ^ 2 * j.totient → n ≠ j + (c ^ 2 * j.totient - 2 * c))) →
    0 < OeisA234246.a n

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_1 := by
  intro h₁ h₂ n hn hd
  by_cases h : ∃ j c : ℕ, 0 < j ∧ 0 < c ∧ (n = j + (c ^ 2 * j.totient + 2 * c) ∨
      (2 * c < c ^ 2 * j.totient ∧ n = j + (c ^ 2 * j.totient - 2 * c)))
  · obtain ⟨j, c, hj, hc, h | ⟨hlt, h⟩⟩ := h
    · exact h ▸ (h₁ j c hj hc).1
    · exact h ▸ (h₁ j c hj hc).2 hlt
  · apply h₂ n hn hd
    intro j c hj hc
    exact ⟨fun he => h ⟨j, c, hj, hc, Or.inl he⟩,
      fun hlt he => h ⟨j, c, hj, hc, Or.inr ⟨hlt, he⟩⟩⟩

end OMA.R_OeisA234246_conjecture_1_R1
