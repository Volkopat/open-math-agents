import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1
import Mathlib

/-! Peel the 53 residual encodings from classify. Non-residual good machines
must still admit a depth-20 backward certificate or a FAR reader pair. -/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H1_R1
open Turing Turing.BusyBeaver

private def entry (z : ℕ) : Machine (Fin 2) (Fin 4) := fun r s =>
  let k := z / 17 ^ (2 * r.val + s.val) % 17
  if k = 16 then none
  else some (some (Fin.ofNat 4 (k / 4)),
    .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))

private def residuals : List ℕ :=
  [192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
   1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,
   3133858477, 3267241361, 3267325035, 3267408318, 3267408386, 3268076724,
   3268179812, 3268243766, 3325136085, 3330584823, 3330638645, 3475567181,
   3475567351, 3672067699, 3673413691, 3673413861, 4079576433, 4093775003,
   4100731862, 4498257380, 4684022874, 4953712200, 4972106404, 4972170205,
   5435078199, 5439716071, 5439804454, 5440806757, 5453953928, 5537278425,
   5792616725, 6328050068, 6695802976, 6734875946, 6734876082, 6734876116,
   6745900956, 6746235074, 6775658997, 6778655859, 6852444036]

/-- Non-residual classify: backward or FAR. -/
def H1 : Prop :=
  ∀ M : Machine (Fin 2) (Fin 4),
    let run := M.multiStep (Machine.init [])
    M 0 0 = some (some 1, .write 0 .right) →
    M 1 0 = some (some 2, .write 1 .left) →
    (∃ q t, run 107 = some ⟨some q, t⟩) →
    (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
        run i = some ⟨some q, t⟩ ∧ t.head = a) ↔
        ∃ q' z, M q a = some (some q', z)) →
    (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
    (∀ i p q a (side : Bool) (w : List (Fin 2)) f, 0 < p → i + p ≤ 107 →
      let c := fun t : ListBlank (Fin 2) =>
        let free := w.foldr ListBlank.cons t
        (⟨some q, if side then ⟨a, free, f⟩ else ⟨a, f, free⟩⟩ : Cfg (Fin 2) (Fin 4))
      (∃ t, run i = some (c t)) →
      ¬ ∀ t, ∃ u, M.multiStep (c t) p = some (c u)) →
    (∀ z ∈ residuals, M ≠ entry z) →
    (∃ k ≤ 20, ∀ u v, M.multiStep u k = some v → (M.step v).isSome) ∨
      ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
          (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
          L 0 x = x ∧ R 0 y = y ∧ S 0 0 x y = true ∧
          ∀ q a s t i j, S q a (L s i) (R t j) = true →
            ∃ r w d, M q a = some (some r, Stmt.write w d) ∧
              (match d with
               | .left => S r s i (R w (R t j))
               | .right => S r t (L w (L s i)) j) = true

/-- Residuals-only side obligation kept distinct for the reduction API. -/
def H2 : Prop :=
  ∀ z ∈ residuals, entry z = entry z

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1.H1 := by
  intro h _ M run hA hB live used form loopfree
  by_cases hz : ∃ z ∈ residuals, M = entry z
  · obtain ⟨z, hmem, rfl⟩ := hz
    exact Or.inr (Or.inl ⟨z, hmem, rfl⟩)
  · have hne : ∀ z ∈ residuals, M ≠ entry z := fun z hmem eq => hz ⟨z, hmem, eq⟩
    -- H1 uses the same let-run binder shape; apply with the exposed `run`.
    exact (h M hA hB live used form loopfree hne).elim Or.inl fun hf => Or.inr (Or.inr hf)

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H1_R1
