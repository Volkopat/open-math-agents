import OMAReductions.R_oeis_a203914_R1

/-!
# A203914, step R1.H1: hardness of better-than-`alphaGW` Max Cut, split in three
Credit: @my-other-github-account

`R1.H1` says that a polynomial-time `α`-approximation for Max Cut with `α > alphaGW` gives
`P = NP`. This reduction separates the three independent ingredients.

* H1 (gap hardness, without the Unique Games Conjecture). For every `alphaGW < α ≤ 1` and every
  NP language `L` there are rationals `0 ≤ s`, `0 < c` with `s < α c` and a polynomial-time map
  from words to scaled graphs (scale `Q > 0`, graph on `Fin n`; output: `n`, `Q`, then the
  adjacency matrix) whose maximum cut is at least `c Q` on YES inputs and at most `s Q` on NO
  inputs. This is the OpenAI formalization `OAI.OptimalMaxCut.main` (openai/math, commit
  3344da59991e, Apache-2.0), a gap reduction from binary 3SAT, composed with Cook–Levin.
* H2 (threshold test). Running a polynomial-time algorithm on the produced graph and comparing
  the size of the cut it returns with `s Q` is a polynomial-time decision procedure.
* H3. `P ⊆ NP`.

`main`: clamp `α` to `β = min α 1`; an `α`-approximate cut is `β`-approximate. On YES inputs the
returned cut has size at least `β c Q > s Q`; on NO inputs it has size at most the maximum
cut, hence at most `s Q`. So the threshold test decides `L`, and `NP ⊆ P`.
-/

namespace OMA.R_oeis_a203914_R1_H1_R1

open OMA.S_oeis_a203914 Turing

def H1 : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → ∀ L ∈ NP, ∃ (c s : ℚ)
    (f : List Bool → ℕ × Σ n : ℕ, SimpleGraph (Fin n)),
    0 < c ∧ 0 ≤ s ∧ (s : ℝ) < α * c ∧
    Nonempty (TM2ComputableInPolyTime id
      (fun p : ℕ × Σ n : ℕ, SimpleGraph (Fin n) => natBits p.2.1 ++ natBits p.1 ++ graphBits p.2.2)
      f) ∧
    ∀ x, 0 < (f x).1 ∧
      (L x = true → (c : ℝ) * (f x).1 ≤ (maxCut (f x).2.2 : ℝ)) ∧
      (L x = false → (maxCut (f x).2.2 : ℝ) ≤ (s : ℝ) * (f x).1)

def H2 : Prop :=
  ∀ s : ℚ, 0 ≤ s → ∀ (f : List Bool → ℕ × Σ n : ℕ, SimpleGraph (Fin n))
    (alg : List Bool → List Bool),
    Nonempty (TM2ComputableInPolyTime id
      (fun p : ℕ × Σ n : ℕ, SimpleGraph (Fin n) => natBits p.2.1 ++ natBits p.1 ++ graphBits p.2.2)
      f) →
    Nonempty (TM2ComputableInPolyTime id id alg) →
    (fun x => decide (s * ((f x).1 : ℚ) < (cutSize (f x).2.2
      (fun i => (alg (graphBits (f x).2.2))[i.val]?.getD false) : ℚ))) ∈ P

def H3 : Prop :=
  P ⊆ NP

theorem main : H1 → H2 → H3 → OMA.R_oeis_a203914_R1.H1 := by
  intro h1 h2 h3 α hα happ
  obtain ⟨alg, hm, hspec⟩ := happ
  have hβ : alphaGW < min α 1 := lt_min hα OMA.R_oeis_a203914_R1.alphaGW_lt_one
  apply Set.Subset.antisymm h3
  intro L hL
  obtain ⟨c, s, f, hc, hs, hgap, hf, hx⟩ := h1 (min α 1) hβ (min_le_right _ _) L hL
  have hd := h2 s hs f alg hf hm
  have key : (fun x => decide (s * ((f x).1 : ℚ) < (cutSize (f x).2.2
      (fun i => (alg (graphBits (f x).2.2))[i.val]?.getD false) : ℚ))) = L := by
    funext x
    obtain ⟨hpos, hyes, hno⟩ := hx x
    obtain ⟨cut, hout, hcut⟩ := hspec _ (f x).2.2
    have hget : (fun i : Fin (f x).2.1 => (alg (graphBits (f x).2.2))[i.val]?.getD false) = cut := by
      funext i
      rw [hout]
      simp
    rw [hget]
    have hle : cutSize (f x).2.2 cut ≤ maxCut (f x).2.2 :=
      Finset.le_sup (f := cutSize (f x).2.2) (Finset.mem_univ cut)
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
    have hQ : (0 : ℝ) < (f x).1 := by exact_mod_cast hpos
    have hβpos : 0 < min α 1 := by
      by_contra hn
      have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) hcR.le
      linarith
    have hbeta : min α 1 * (maxCut (f x).2.2 : ℝ) ≤ (cutSize (f x).2.2 cut : ℝ) :=
      (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hcut
    have hiff : ((s : ℝ) * (f x).1 < (cutSize (f x).2.2 cut : ℝ)) ↔
        (s * ((f x).1 : ℚ) < (cutSize (f x).2.2 cut : ℚ)) := by
      constructor <;> intro h <;> exact_mod_cast h
    cases hLx : L x
    · have hb := hno hLx
      have hleR : (cutSize (f x).2.2 cut : ℝ) ≤ (maxCut (f x).2.2 : ℝ) := by exact_mod_cast hle
      rw [decide_eq_false_iff_not, ← hiff, not_lt]
      exact hleR.trans hb
    · have hb := hyes hLx
      rw [decide_eq_true_iff, ← hiff]
      calc (s : ℝ) * (f x).1 < (min α 1 * c) * (f x).1 := mul_lt_mul_of_pos_right hgap hQ
        _ = min α 1 * ((c : ℝ) * (f x).1) := mul_assoc _ _ _
        _ ≤ min α 1 * (maxCut (f x).2.2 : ℝ) := mul_le_mul_of_nonneg_left hb hβpos.le
        _ ≤ _ := hbeta
  rw [← key]
  exact hd

end OMA.R_oeis_a203914_R1_H1_R1
