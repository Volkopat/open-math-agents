import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1

/-!
# Separation of the three matchings on four tensor sites

The first input asks for one fixed tensor power at which no constant number
of copies suffices throughout the higher powers. The second input is the
strict spectral comparison principle for these four-site tensors. Together
they give a normalized point on Fin 4 violating the tree inequality.
The matching comparison was described by ubuwaits on the Erdős 20 desk.
-/

namespace OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2

def H1 : Prop :=
  let problem {J : Type} [Fintype J] [DecidableEq J] (a b c e : J) : Prop :=
    let T := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
    let one : T := ⟨fun _ => 1, fun _ => 1⟩
    let zero : T := ⟨fun _ => 1, fun _ => 0⟩
    let mul (X Y : T) : T := ⟨fun j => X.1 j * Y.1 j, fun z =>
      X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
      Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩
    let add (X Y : T) : T := ⟨fun j => X.1 j + Y.1 j, fun z =>
      if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
      else if h' : ∀ j, X.1 j ≤ z j then
        Y.2 (fun j => ⟨z j - X.1 j, by
          have : (z j : ℕ) < X.1 j + Y.1 j := (z j).2
          have := h' j
          omega⟩) else 0⟩
    let res (Y X : T) := ∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
      ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z
    let wire (a b : J) : T := ⟨fun j => if j = a ∨ j = b then 2 else 1,
      fun z => if (z a : ℕ) = z b then 1 else 0⟩
    let power (X : T) (n : ℕ) := Nat.rec one (fun _ Z => mul Z X) n
    let copies (X : T) (c : ℕ) := Nat.rec zero (fun _ Z => add Z X) c
    let U := mul (wire a b) (wire c e)
    let V := mul (wire a c) (wire b e)
    let W := mul (wire a e) (wire b c)
    let test (k C n : ℕ) := res (power (power U k) n)
      (copies (power (add (power V k) (power W k)) n) C)
    ∃ k : ℕ, 2 ≤ k ∧ ∀ C : ℕ, 0 < C → ∃ n : ℕ, 0 < n ∧ ¬ test k C n
  problem (0 : Fin 4) 1 2 3

def H2 : Prop :=
  let problem {J : Type} [Fintype J] [DecidableEq J] (a b c e : J) : Prop :=
    let T := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ
    let one : T := ⟨fun _ => 1, fun _ => 1⟩
    let zero : T := ⟨fun _ => 1, fun _ => 0⟩
    let mul (X Y : T) : T := ⟨fun j => X.1 j * Y.1 j, fun z =>
      X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
      Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩
    let add (X Y : T) : T := ⟨fun j => X.1 j + Y.1 j, fun z =>
      if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
      else if h' : ∀ j, X.1 j ≤ z j then
        Y.2 (fun j => ⟨z j - X.1 j, by
          have : (z j : ℕ) < X.1 j + Y.1 j := (z j).2
          have := h' j
          omega⟩) else 0⟩
    let res (Y X : T) := ∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
      ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z
    let wire (a b : J) : T := ⟨fun j => if j = a ∨ j = b then 2 else 1,
      fun z => if (z a : ℕ) = z b then 1 else 0⟩
    let power (X : T) (n : ℕ) := Nat.rec one (fun _ Z => mul Z X) n
    let copies (X : T) (c : ℕ) := Nat.rec zero (fun _ Z => add Z X) c
    let U := mul (wire a b) (wire c e)
    let V := mul (wire a c) (wire b e)
    let W := mul (wire a e) (wire b c)
    let test (k C n : ℕ) := res (power (power U k) n)
      (copies (power (add (power V k) (power W k)) n) C)
    let P (F : T → ℝ) :=
      (∀ X, 0 ≤ F X) ∧ F one = 1 ∧ (∀ X : T, (∀ z, X.2 z = 0) → F X = 0) ∧
      (∀ X Y, res Y X → F Y ≤ F X) ∧
      (∀ X Y, F (mul X Y) = F X * F Y) ∧ ∀ X Y, F (add X Y) = F X + F Y
    (∀ F : T → ℝ, P F →
      let d := fun a b => Real.logb 2 (F (wire a b))
      d a b + d c e ≤ max (d a c + d b e) (d a e + d b c)) →
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → test k C n
  problem (0 : Fin 4) 1 2 3

theorem main : H1 → H2 → OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1.H1 := by
  intro hgap hcomparison
  by_contra noWitness
  obtain ⟨k, hk, fails⟩ := hgap
  have comps := hcomparison (by
    intro F hF
    by_contra bad
    apply noWitness
    exact ⟨Fin 4, inferInstance, inferInstance, F, hF, 0, 1, 2, 3, lt_of_not_ge bad⟩) k hk
  obtain ⟨C, hC, succeeds⟩ := comps
  obtain ⟨n, hn, failure⟩ := fails C hC
  exact failure (succeeds n hn)

end OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2
