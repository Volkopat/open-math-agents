import OMAReductions.R_Erdos535_erdos_535_R2_H1_R1_H1_R1_H1_R1

-- Reduction Erdos20.erdos_20.R1.H2.R1.H1.R1.H2.R1 of step Erdos20.erdos_20.R1.H2.R1.H1.R1.H2
-- Credit: @LordMike
-- Port of reductions/Erdos20.erdos_20.R1.H2.R1.H1.R1.H2.R1.lean by its author onto the identical hypothesis statement Erdos535.erdos_535.R2.H1.R1.H1.R1.H1.R1.H2.

/-!
# Planar spectral prices: the spectral interval lemma, joint convexity, submodularity, the plane

Source: OpenAI, *Euclidean geometry in the asymptotic spectrum of tensors* and *An exponential bound for
sunflowers* (OpenAI Math Release, Nov 2026), formalized in Lean 4 in github.com/openai/math (Apache-2.0).
The parent step asks, given one spectral point whose wire distance violates the four-point condition, for a
set function `δ` on finite planar sets with the diagonal price laws and, for every finite planar placement,
a spectral point whose one-bit prices are the ratios of `δ`. In OpenAI's proof `δ` is the binary diagonal
price `SpectralPlacementPrices.diagonal` of a planar family of placement prices. The split below separates
the four ingredients of that proof; every hypothesis uses the encoding of the parent step (tensors `⟨d, T⟩`
on a finite site type, spectral points `P`, wire distances `W` = binary log-price of one shared bit).

- `H1` (pure spectral facts, `SiteTensor.exists_spectral_interval_point` and
 `SiteTensor.rawWireDistance_synchronized`): a spectral point on `I` extends to `Option I` with a new site
 at prescribed wire distances `x, y` from `a, b` whenever `x + y = W a b`; and wire distances are
 synchronized along wire-geodesic fractions.
- `H2` (joint convexity, `SiteTensor.rawDiagonalJointConvexity`): any `δ` that is monotone, equal to `dist`
 on pairs and has the planar spectral points is jointly convex. Proof idea: place all points of `Q` at once;
 the fraction conditions on wire distances hold because `δ {p, q} = dist p q`.
- `H3` (`commonLabel_value_le`, `two_le_sum_wire_logs`): the same hypotheses give intersecting
 submodularity (diminishing increments of mask-diagonal log-prices) and the half-perimeter bound on triangles.
- `H4` (the plane, `realize_finite_point_geodesic`, `SpectralPlacementPrices.catZero`,
 `spectralPlane_of_fourPointDefect`, `exists_point_diagonal_map`): given the facts of `H1`, a four-point
 defect yields a monotone `δ`, equal to `dist` on pairs, with the planar spectral points.
-/

namespace OMA.R_Erdos535_erdos_535_R2_H1_R1_H1_R1_H1_R1_H2_R1

def H1 : Prop :=
 let T := fun J : Type => Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
 let P : ∀ (J : Type) [Fintype J] [DecidableEq J], (T J → ℝ) → Prop := fun J _ _ Φ =>
 (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧ (∀ X : T J, (∀ z, X.2 z = 0) → Φ X = 0) ∧
 (∀ X Y : T J, (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 (∀ X Y : T J, Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
 ∀ X Y : T J, Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
 else if h' : ∀ j, X.1 j ≤ z j then Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y
 let W : ∀ {J : Type} [DecidableEq J], (T J → ℝ) → J → J → ℝ :=
 fun Φ s t => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩)
 (∀ (I : Type) [Fintype I] [DecidableEq I] Φ, P I Φ → ∀ (a b : I) (x y : ℝ), 0 ≤ x → 0 ≤ y → x + y = W Φ a b →
 ∃ Ψ, P (Option I) Ψ ∧ (∀ X : T I, Ψ ⟨fun o => o.elim 1 X.1, fun z => X.2 (fun i => z (some i))⟩ = Φ X) ∧ W Ψ none (some a) = x ∧ W Ψ none (some b) = y) ∧
 (∀ (J : Type) [Fintype J] [DecidableEq J] Φ, P J Φ → ∀ (a b c d z w : J) (u : ℝ), 0 ≤ u → u ≤ 1 →
 W Φ a z = u * W Φ a b → W Φ z b = (1-u) * W Φ a b → W Φ c w = u * W Φ c d → W Φ w d = (1-u) * W Φ c d → W Φ z w ≤ (1-u) * W Φ a c + u * W Φ b d)

def H2 : Prop :=
 let T := fun J : Type => Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
 let E := EuclideanSpace ℝ (Fin 2)
 let P : ∀ (J : Type) [Fintype J] [DecidableEq J], (T J → ℝ) → Prop := fun J _ _ Φ =>
 (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧ (∀ X : T J, (∀ z, X.2 z = 0) → Φ X = 0) ∧
 (∀ X Y : T J, (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 (∀ X Y : T J, Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
 ∀ X Y : T J, Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
 else if h' : ∀ j, X.1 j ≤ z j then Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y
 ∀ δ : Finset E → ℝ, Monotone δ → (∀ p q, δ {p, q} = dist p q) →
 (∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ E), ∃ Ψ, P I Ψ ∧ ∀ S : Finset I, S.Nonempty →
 Real.logb 2 (Ψ ⟨fun i => if i ∈ S then 2 else 1, fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) = δ (S.image x) / δ (Finset.univ.image x)) →
 ∀ Q : Finset (E × E), ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
 δ (Q.image fun q => s • q.1 + t • q.2) ≤ s * δ (Q.image Prod.fst) + t * δ (Q.image Prod.snd)

def H3 : Prop :=
 let T := fun J : Type => Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
 let E := EuclideanSpace ℝ (Fin 2)
 let P : ∀ (J : Type) [Fintype J] [DecidableEq J], (T J → ℝ) → Prop := fun J _ _ Φ =>
 (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧ (∀ X : T J, (∀ z, X.2 z = 0) → Φ X = 0) ∧
 (∀ X Y : T J, (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 (∀ X Y : T J, Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
 ∀ X Y : T J, Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
 else if h' : ∀ j, X.1 j ≤ z j then Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y
 ∀ δ : Finset E → ℝ, Monotone δ → (∀ p q, δ {p, q} = dist p q) →
 (∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ E), ∃ Ψ, P I Ψ ∧ ∀ S : Finset I, S.Nonempty →
 Real.logb 2 (Ψ ⟨fun i => if i ∈ S then 2 else 1, fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) = δ (S.image x) / δ (Finset.univ.image x)) →
 (∀ A B : Finset E, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B) ∧
 ∀ p q r, δ {p, q, r} ≤ (dist p q + dist q r + dist r p) / 2

def H4 : Prop :=
 let T := fun J : Type => Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
 let E := EuclideanSpace ℝ (Fin 2)
 let P : ∀ (J : Type) [Fintype J] [DecidableEq J], (T J → ℝ) → Prop := fun J _ _ Φ =>
 (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧ (∀ X : T J, (∀ z, X.2 z = 0) → Φ X = 0) ∧
 (∀ X Y : T J, (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 (∀ X Y : T J, Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
 ∀ X Y : T J, Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
 else if h' : ∀ j, X.1 j ≤ z j then Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y
 let W : ∀ {J : Type} [DecidableEq J], (T J → ℝ) → J → J → ℝ :=
 fun Φ s t => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩)
 (∀ (I : Type) [Fintype I] [DecidableEq I] Φ, P I Φ → ∀ (a b : I) (x y : ℝ), 0 ≤ x → 0 ≤ y → x + y = W Φ a b →
 ∃ Ψ, P (Option I) Ψ ∧ (∀ X : T I, Ψ ⟨fun o => o.elim 1 X.1, fun z => X.2 (fun i => z (some i))⟩ = Φ X) ∧ W Ψ none (some a) = x ∧ W Ψ none (some b) = y) ∧
 (∀ (J : Type) [Fintype J] [DecidableEq J] Φ, P J Φ → ∀ (a b c d z w : J) (u : ℝ), 0 ≤ u → u ≤ 1 →
 W Φ a z = u * W Φ a b → W Φ z b = (1-u) * W Φ a b → W Φ c w = u * W Φ c d → W Φ w d = (1-u) * W Φ c d → W Φ z w ≤ (1-u) * W Φ a c + u * W Φ b d) →
 ∀ (J : Type) [Fintype J] [DecidableEq J] Φ (a b c e : J), P J Φ → max (W Φ a c + W Φ b e) (W Φ a e + W Φ b c) < W Φ a b + W Φ c e →
 ∃ δ : Finset E → ℝ, Monotone δ ∧ (∀ p q, δ {p, q} = dist p q) ∧
 ∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ E), ∃ Ψ, P I Ψ ∧ ∀ S : Finset I, S.Nonempty →
 Real.logb 2 (Ψ ⟨fun i => if i ∈ S then 2 else 1, fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) = δ (S.image x) / δ (Finset.univ.image x)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos535_erdos_535_R2_H1_R1_H1_R1_H1_R1.H2 := by
 intro h1 h2 h3 h4 J _ _ Φ a b c e hP hv
 obtain ⟨δ, hm, hp, hΨ⟩ := h4 h1 J Φ a b c e hP hv
 exact ⟨δ, hm, (h3 δ hm hp hΨ).1, h2 δ hm hp hΨ, hp, (h3 δ hm hp hΨ).2, hΨ⟩

end OMA.R_Erdos535_erdos_535_R2_H1_R1_H1_R1_H1_R1_H2_R1
