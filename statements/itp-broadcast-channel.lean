import Mathlib

/-!
# Capacity region of the two-receiver broadcast channel

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/broadcast-channel.md
Credit: @eltociear

Adapted from the source's own Lean module `InfoTheory.Problems.BroadcastChannel`
(`Statement : ∀ kX kY₁ kY₂ W, bcCapacityRegion W = martonInnerBound W`) and its
`Core.Entropy` / `Core.Channels` definitions, inlined here with plain real-valued pmfs.

The source asks for a single-letter characterization of the capacity region of a general
two-receiver discrete memoryless broadcast channel; its formal reading is the conjecture that
Marton's inner bound (with the common auxiliary `W`, El Gamal–Kim Prop. 8.1) equals the
capacity region for every finite-alphabet channel. Note: the source records an unrefereed
2026 claim (Huang–Liu–Liu, arXiv:2608.19869) that this equality fails for some channel,
so the statement may well be false; it is stated as the source states it.

Conventions (as in the source): entropies in bits; rates are achievable when, for every
`ε > 0` and all large `n`, there is a code with `max 1 ⌊2^{nRᵢ}⌋` messages for receiver `i`
whose average (over both messages) probability of error is at most `ε`; the capacity
region is the closure of the achievable pairs.
-/

open scoped BigOperators Classical

namespace OMA.S_itp_broadcast_channel

/-- Shannon entropy in bits of a finite real-valued pmf (`-p log₂ p`, with `0 log 0 = 0`). -/
noncomputable def ent {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a) / Real.log 2

/-- Pushforward of a finite pmf along `f`. -/
noncomputable def push {α β : Type*} [Fintype α] (f : α → β) (p : α → ℝ) : β → ℝ :=
  fun b => ∑ a, if f a = b then p a else 0

/-- Mutual information `I(A; B)` of a joint pmf on `α × β`. -/
noncomputable def mi {α β : Type*} [Fintype α] [Fintype β] (p : α × β → ℝ) : ℝ :=
  ent (push Prod.fst p) + ent (push Prod.snd p) - ent p

/-- Conditional mutual information `I(A; B | C)` of a joint pmf on `α × β × γ`. -/
noncomputable def cmi {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : ℝ :=
  ent (push (fun t => (t.1, t.2.2)) p) + ent (push (fun t => (t.2.1, t.2.2)) p)
    - ent p - ent (push (fun t => t.2.2) p)

/-- `W` is a discrete memoryless broadcast channel `p(y₁, y₂ | x)`: a stochastic matrix. -/
def IsBC {X Y₁ Y₂ : Type*} [Fintype Y₁] [Fintype Y₂] (W : X → Y₁ × Y₂ → ℝ) : Prop :=
  (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1

/-- Operational achievability of `(R₁, R₂)` over the broadcast channel `W` (private messages
    `m₁`, `m₂`; receiver `i` decodes `mᵢ` from `Yᵢⁿ`; average error probability). -/
def IsBCAchievable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : X → Y₁ × Y₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂),
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
           then ∏ i : Fin n, W (enc m₁ m₂ i) (y i) else 0) ≤ ε

/-- Capacity region: the closure of the operationally achievable rate pairs. -/
def bcCapacityRegion {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : X → Y₁ × Y₂ → ℝ) : Set (ℝ × ℝ) :=
  closure { p | IsBCAchievable W p.1 p.2 }

/-- Marton's inner bound with a common auxiliary `W` (here `Q`, to avoid a clash with the
    channel's name) and private auxiliaries `U, V`, over all finite auxiliary alphabets and all
    joint pmfs `p(q, u, v, x)` followed by the channel, closed topologically:
    `R₁ ≤ I(Q,U;Y₁)`, `R₂ ≤ I(Q,V;Y₂)`,
    `R₁ + R₂ ≤ I(Q,U;Y₁) + I(V;Y₂|Q) - I(U;V|Q)`,
    `R₁ + R₂ ≤ I(U;Y₁|Q) + I(Q,V;Y₂) - I(U;V|Q)`. -/
def martonInnerBound {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : X → Y₁ × Y₂ → ℝ) : Set (ℝ × ℝ) :=
  closure { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ (kQ kU kV : ℕ) (P : Fin kQ × Fin kU × Fin kV × X → ℝ),
      (∀ t, 0 ≤ P t) ∧ (∑ t, P t = 1) ∧
      let joint : (Fin kQ × Fin kU × Fin kV × X) × (Y₁ × Y₂) → ℝ :=
        fun z => P z.1 * W z.1.2.2.2 z.2
      let IQU_Y1 := mi (push (fun z => ((z.1.1, z.1.2.1), z.2.1)) joint)
      let IQV_Y2 := mi (push (fun z => ((z.1.1, z.1.2.2.1), z.2.2)) joint)
      let IU_Y1_Q := cmi (push (fun z => (z.1.2.1, z.2.1, z.1.1)) joint)
      let IV_Y2_Q := cmi (push (fun z => (z.1.2.2.1, z.2.2, z.1.1)) joint)
      let IUV_Q := cmi (push (fun t => (t.2.1, t.2.2.1, t.1)) P)
      p.1 ≤ IQU_Y1 ∧ p.2 ≤ IQV_Y2 ∧
      p.1 + p.2 ≤ IQU_Y1 + IV_Y2_Q - IUV_Q ∧
      p.1 + p.2 ≤ IU_Y1_Q + IQV_Y2 - IUV_Q }

/-- Marton's inner bound is the capacity region of every finite-alphabet two-receiver
    discrete memoryless broadcast channel. -/
theorem main :
    ∀ (kX kY₁ kY₂ : ℕ) (W : Fin kX → Fin kY₁ × Fin kY₂ → ℝ), IsBC W →
      bcCapacityRegion W = martonInnerBound W := by
  sorry

end OMA.S_itp_broadcast_channel
