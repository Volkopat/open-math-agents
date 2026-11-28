import OMAStatements.S_oeis_a289057

-- Problem: A289057: Fixed point of the mapping 00->0010, 01->010, 10->011, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a289057.lean:0 (declaration OMA.S_oeis_a289057.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let P be the 32-letter prefix of w(6) = P ++ 1^4, and define
-- block k = 1^(k+1) 0 1^(k+3) 0 1^(k+3) 0 1^(k+2) 0 of length 4k + 13.
-- Since P ends at a clean pair boundary, step (P ++ r) = P ++ block 0 ++ 11 ++ step r for all r,
-- and 11 ++ step (block k ++ r) = block (k + 1) ++ 11 ++ step r because step maps 1^(a+1) 0 to
-- 1^a 0 1 1. By induction on m, w(m + 6) = P ++ block 0 ++ ... ++ block (m - 1) ++ 1^(2m + 4),
-- whose length is 32 + m(2m + 11) + (2m + 4) = 2m^2 + 13m + 36 = A289060(m + 6).

namespace ProofA289057

open OMA.S_oeis_a289057

def ones (k : ℕ) : List Bool := List.replicate k true

def block (k : ℕ) : List Bool :=
  ones (k + 1) ++ (false :: (ones (k + 3) ++ (false :: (ones (k + 3) ++ (false :: (ones (k + 2) ++ [false]))))))

def P : List Bool :=
  [false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, false, true, false]

def chainFrom (k : ℕ) : ℕ → List Bool
  | 0 => []
  | m + 1 => block k ++ chainFrom (k + 1) m

theorem step_11 (r : List Bool) : step (true :: true :: r) = true :: step (true :: r) := rfl

theorem step_ones_zero : ∀ (k : ℕ) (r : List Bool),
    step (ones (k + 1) ++ false :: r) = ones k ++ false :: true :: true :: step r
  | 0, _ => rfl
  | k + 1, r => by
    show step (true :: true :: (ones k ++ false :: r)) =
      true :: (ones k ++ false :: true :: true :: step r)
    rw [step_11]
    exact congrArg (List.cons true) (step_ones_zero k r)

theorem step_ones : ∀ k : ℕ, step (ones k) = ones k
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show step (true :: true :: ones k) = true :: true :: ones k
    rw [step_11]
    exact congrArg (List.cons true) (step_ones (k + 1))

theorem step_block (k : ℕ) (r : List Bool) :
    true :: true :: step (block k ++ r) = block (k + 1) ++ true :: true :: step r := by
  simp only [block, List.append_assoc, List.cons_append, List.nil_append]
  rw [step_ones_zero, step_ones_zero, step_ones_zero, step_ones_zero]
  rfl

theorem step_P (r : List Bool) : step (P ++ r) = P ++ block 0 ++ true :: true :: step r := rfl

theorem step_chainFrom (m : ℕ) : ∀ (k : ℕ) (r : List Bool),
    true :: true :: step (chainFrom k m ++ r) = chainFrom (k + 1) m ++ true :: true :: step r := by
  induction m with
  | zero =>
    intro k r
    rfl
  | succ m ih =>
    intro k r
    show true :: true :: step ((block k ++ chainFrom (k + 1) m) ++ r) =
      (block (k + 1) ++ chainFrom (k + 2) m) ++ true :: true :: step r
    rw [List.append_assoc, step_block, List.append_assoc, ih (k + 1) r]

theorem w_six : w 6 = P ++ ones 4 := by decide

theorem w_form : ∀ m : ℕ, w (m + 6) = P ++ chainFrom 0 m ++ ones (2 * m + 4)
  | 0 => by
    show w 6 = P ++ [] ++ ones 4
    rw [List.append_nil]
    exact w_six
  | m + 1 => by
    have ih := w_form m
    show step (w (m + 6)) = P ++ (block 0 ++ chainFrom 1 m) ++ ones (2 * (m + 1) + 4)
    rw [ih, List.append_assoc, step_P]
    rw [show P ++ block 0 ++ true :: true :: step (chainFrom 0 m ++ ones (2 * m + 4)) =
      P ++ block 0 ++ (true :: true :: step (chainFrom 0 m ++ ones (2 * m + 4))) from rfl]
    rw [step_chainFrom m 0 (ones (2 * m + 4)), step_ones]
    simp only [List.append_assoc]
    rfl

theorem len_ones (k : ℕ) : (ones k).length = k := List.length_replicate

theorem len_block (k : ℕ) : (block k).length = 4 * k + 13 := by
  simp only [block, List.length_append, List.length_cons, List.length_nil, len_ones]
  omega

theorem len_chainFrom (m : ℕ) : ∀ k : ℕ, (chainFrom k m).length = m * (4 * k + 2 * m + 11) := by
  induction m with
  | zero =>
    intro k
    exact (Nat.zero_mul _).symm
  | succ m ih =>
    intro k
    show (block k ++ chainFrom (k + 1) m).length = (m + 1) * (4 * k + 2 * (m + 1) + 11)
    rw [List.length_append, len_block, ih (k + 1)]
    ring

theorem len_P : P.length = 32 := rfl

theorem len_w_ge6 (m : ℕ) : ((w (m + 6)).length : ℤ) = 2 * (m : ℤ) ^ 2 + 13 * m + 36 := by
  rw [w_form m, List.length_append, List.length_append, len_P, len_chainFrom m 0, len_ones]
  push_cast
  ring

theorem A289060_ge5 : ∀ m : ℕ,
    A289060 (m + 5) = 2 * (m : ℤ) ^ 2 + 9 * m + 25 ∧
    A289060 (m + 6) = 2 * (m : ℤ) ^ 2 + 13 * m + 36 ∧
    A289060 (m + 7) = 2 * (m : ℤ) ^ 2 + 17 * m + 51
  | 0 => ⟨rfl, rfl, rfl⟩
  | m + 1 => by
    obtain ⟨h0, h1, h2⟩ := A289060_ge5 m
    refine ⟨?_, ?_, ?_⟩
    · rw [show m + 1 + 5 = m + 6 by omega, h1]
      push_cast
      ring
    · rw [show m + 1 + 6 = m + 7 by omega, h2]
      push_cast
      ring
    · show A289060 (m + 8) = 2 * ((m + 1 : ℕ) : ℤ) ^ 2 + 17 * ((m + 1 : ℕ) : ℤ) + 51
      have hrec : A289060 (m + 8) =
          3 * A289060 (m + 7) - 3 * A289060 (m + 6) + A289060 (m + 5) := rfl
      rw [hrec, h2, h1, h0]
      push_cast
      ring

end ProofA289057

open OMA.S_oeis_a289057 ProofA289057 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289057.main := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | m + 6 => rw [len_w_ge6 m, (A289060_ge5 m).2.1]
