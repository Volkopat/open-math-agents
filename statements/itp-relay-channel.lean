import Mathlib

/-!
# Capacity of the relay channel

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/relay-channel.md
Credit: @eltociear

Adapted from the source's own Lean module `InfoTheory.Problems.RelayChannel`
(`Statement : ∀ kX kXr kY kYr (W : RelayChannel …), relayCapacity W = coverElGamalTheorem7Rate W`,
in its statement-fixed form of 2026-11-27) and the `Core.Entropy` / `Core.Channels`
definitions it uses (`ProbDist`, `DMC`, `condMutualInfo`, `IsRelayAchievable`,
`relayCapacity`), inlined here with plain real-valued pmfs and stochastic matrices.

The source asks for a single-letter characterization of the capacity of the general discrete
memoryless relay channel `p(y, y_r | x, x_r)` (van der Meulen 1971). Its formal reading is:
does Cover–El Gamal's Theorem 7 (partial decode-forward combined with compress-forward, with
time sharing), in the three-constraint form of Chong–Motani (2011, Lemma 2) and
El Gamal–Gohari–Nair (Theorem 1), achieve the capacity of every finite-alphabet DM relay
channel? `R_Thm7` is the supremum of `min(c₁, c₂, c₃)` with
* `c₁ = I(X, X_r; Y | Q) - I(Y_r; V | U, X, X_r, Y, Q)`,
* `c₂ = I(X; V, Y | U, X_r, Q) + I(U; Y_r | W, X_r, Q)`,
* `c₃ = c₂ + I(X_r; Y | W, Q) - I(Y_r; V | U, X_r, Y, Q)`,

over all finite auxiliary alphabets and joint laws
`p(q) p(w|q) p(u|w,q) p(x|u,q) p(x_r|w,q) p(y, y_r | x, x_r) p(v|u,x_r,y_r,q)`.
(The auxiliary `W` of the source is called `Wa` here, since `W` is the channel.)

Conventions (as in the source): entropies in bits; a rate `R ≥ 0` is achievable when for every
`ε > 0` and all large `n` there is a code with `max 1 ⌊2^{nR}⌋` messages, an encoder
`Fin n → X` per message, a causal relay (`X_{r,i}` is a function of `Y_r^{i-1}`) and a decoder
of `Yⁿ`, whose average probability of error is at most `ε`; the capacity is the supremum of the
achievable rates. Both sides lie in `[0, log₂ |Y|]` (source, `Known.Certificates.RelayChannel`).
-/

open scoped BigOperators Classical

namespace OMA.S_itp_relay_channel

/-- Shannon entropy in bits of a finite real-valued pmf (`-p log₂ p`, with `0 log 0 = 0`). -/
noncomputable def ent {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a) / Real.log 2

/-- Pushforward of a finite pmf along `f`. -/
noncomputable def push {α β : Type*} [Fintype α] (f : α → β) (p : α → ℝ) : β → ℝ :=
  fun b => ∑ a, if f a = b then p a else 0

/-- Conditional mutual information `I(A; B | C)` of a joint pmf on `α × β × γ`. -/
noncomputable def cmi {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : ℝ :=
  ent (push (fun t => (t.1, t.2.2)) p) + ent (push (fun t => (t.2.1, t.2.2)) p)
    - ent p - ent (push (fun t => t.2.2) p)

/-- `p` is a probability mass function on the finite type `α`. -/
def IsPmf {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- `K` is a stochastic matrix (a discrete memoryless channel `K(b | a)`). -/
def IsKernel {α β : Type*} [Fintype β] (K : α → β → ℝ) : Prop :=
  (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1

/-- Operational achievability of rate `R` over the DM relay channel `W(y, y_r | x, x_r)`:
    deterministic encoder, causal relay (`relay i` sees `y_r` at times `< i`), decoder of `yⁿ`,
    average error probability over the `max 1 ⌊2^{nR}⌋` messages at most `ε`. -/
def IsRelayAchievable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : X × Xr → Y × Yr → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : Fin M → Fin n → X)
      (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
      (dec : (Fin n → Y) → Fin M),
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          (if dec y ≠ m then
            ∏ i : Fin n, W (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩))
              (y i, yr i)
          else 0) ≤ ε

/-- Capacity `C(W)` of a DM relay channel: the supremum of the achievable rates. -/
noncomputable def relayCapacity {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr] (W : X × Xr → Y × Yr → ℝ) : ℝ :=
  sSup { R : ℝ | IsRelayAchievable W R }

/-- Joint law of Theorem 7 on `t = (q, w, u, x, x_r, y, y_r, v)`:
    `p(q) p(w|q) p(u|w,q) p(x|u,q) p(x_r|w,q) W(y, y_r | x, x_r) p(v|u,x_r,y_r,q)`. -/
noncomputable def thm7Joint {X Xr Y Yr Q Wa U V : Type*}
    (W : X × Xr → Y × Yr → ℝ) (pQ : Q → ℝ) (pW : Q → Wa → ℝ) (pU : Wa × Q → U → ℝ)
    (pX : U × Q → X → ℝ) (pXr : Wa × Q → Xr → ℝ) (pV : U × Xr × Yr × Q → V → ℝ) :
    Q × Wa × U × X × Xr × Y × Yr × V → ℝ :=
  fun ⟨q, w, u, x, xr, y, yr, v⟩ =>
    pQ q * pW q w * pU (w, q) u * pX (u, q) x * pXr (w, q) xr * W (x, xr) (y, yr) *
      pV (u, xr, yr, q) v

/-- The Theorem 7 rate `min(c₁, c₂, c₃)` of a joint pmf on `(q, w, u, x, x_r, y, y_r, v)`. -/
noncomputable def thm7MinRate {X Xr Y Yr Q Wa U V : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    [Fintype Q] [Fintype Wa] [Fintype U] [Fintype V]
    (J : Q × Wa × U × X × Xr × Y × Yr × V → ℝ) : ℝ :=
  -- c₁ = I(X, X_r; Y | Q) - I(Y_r; V | U, X, X_r, Y, Q)
  let c₁ := cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        ((t.2.2.2.1, t.2.2.2.2.1), t.2.2.2.2.2.1, t.1)) J) -
      cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        (t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2,
          (t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.1))) J)
  -- c₂ = I(X; V, Y | U, X_r, Q) + I(U; Y_r | W, X_r, Q)
  let c₂ := cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        (t.2.2.2.1, (t.2.2.2.2.2.2.2, t.2.2.2.2.2.1), (t.2.2.1, t.2.2.2.2.1, t.1))) J) +
      cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        (t.2.2.1, t.2.2.2.2.2.2.1, (t.2.1, t.2.2.2.2.1, t.1))) J)
  -- c₃ = c₂ + I(X_r; Y | W, Q) - I(Y_r; V | U, X_r, Y, Q)
  let c₃ := c₂ +
      cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        (t.2.2.2.2.1, t.2.2.2.2.2.1, (t.2.1, t.1))) J) -
      cmi (push (fun t : Q × Wa × U × X × Xr × Y × Yr × V =>
        (t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2, (t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.1))) J)
  min c₁ (min c₂ c₃)

/-- Cover–El Gamal (1979) Theorem 7 rate, three-constraint form: the supremum of
    `thm7MinRate` over all finite auxiliary alphabets `Fin k` and all kernels of the
    prescribed Markov structure. -/
noncomputable def coverElGamalTheorem7Rate {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr] (W : X × Xr → Y × Yr → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (kQ kW kU kV : ℕ) (pQ : Fin kQ → ℝ) (pW : Fin kQ → Fin kW → ℝ)
    (pU : Fin kW × Fin kQ → Fin kU → ℝ) (pX : Fin kU × Fin kQ → X → ℝ)
    (pXr : Fin kW × Fin kQ → Xr → ℝ) (pV : Fin kU × Xr × Yr × Fin kQ → Fin kV → ℝ),
    IsPmf pQ ∧ IsKernel pW ∧ IsKernel pU ∧ IsKernel pX ∧ IsKernel pXr ∧ IsKernel pV ∧
    r = thm7MinRate (thm7Joint W pQ pW pU pX pXr pV) }

/-- Capacity of the general relay channel (van der Meulen 1971), as the source formalizes it:
    for every finite-alphabet discrete memoryless relay channel `W(y, y_r | x, x_r)`, the
    capacity equals the Cover–El Gamal Theorem 7 rate. -/
theorem main :
    ∀ (kX kXr kY kYr : ℕ) (W : Fin kX × Fin kXr → Fin kY × Fin kYr → ℝ), IsKernel W →
      relayCapacity W = coverElGamalTheorem7Rate W := by
  sorry

end OMA.S_itp_relay_channel
