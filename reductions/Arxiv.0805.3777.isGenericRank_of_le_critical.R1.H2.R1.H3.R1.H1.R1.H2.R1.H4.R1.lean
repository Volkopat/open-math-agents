import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Div

/-! Fixed-slice starting sizes for Friedland's generic-rank problem.
The anchored chart is mattdorman's merged reduction #14831. For each fixed
first dimension n, the first hypothesis asks for finitely many starting sizes.
The second is one geometric propagation law confined to regular width-two steps.
The count cutoff and the parity induction are by xlh1551. -/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1_H4_R1

set_option maxHeartbeats 1000000 in
private theorem short_remainder {numerator denominator linearTerm remainder : ℕ} (hD : 0<denominator) (hE : remainder ≤ denominator)
    (identity : 4*numerator=denominator*linearTerm+remainder) :
    numerator ⌈/⌉ denominator = (linearTerm+(if remainder=0 then 0 else 1)) ⌈/⌉ 4 := by
  have same (q : ℕ) :
      numerator ⌈/⌉ denominator ≤ q ↔ (linearTerm+(if remainder=0 then 0 else 1)) ⌈/⌉ 4 ≤ q := by
    rw [ceilDiv_le_iff_le_mul hD,ceilDiv_le_iff_le_mul (by decide : 0<4)]
    have scale : numerator ≤ denominator*q ↔ denominator*linearTerm+remainder ≤ denominator*(4*q) := by
      rw [← identity,show denominator*(4*q)=4*(denominator*q) by ring]
      omega
    rw [scale]
    by_cases e : remainder=0
    · simp only [e, Nat.add_zero]
      exact mul_le_mul_iff_right₀ hD
    · simp only [if_neg e]
      constructor
      · intro le
        by_contra bad
        have off := Nat.mul_le_mul_left denominator (show 4*q ≤ linearTerm by omega)
        omega
      · intro le
        calc
          denominator*linearTerm+remainder ≤ denominator*(linearTerm+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
          _ ≤ denominator*(4*q) := Nat.mul_le_mul_left denominator le
  exact le_antisymm ((same _).mpr le_rfl) ((same _).mp le_rfl)

/- Here n=a+3. The remainder in polynomial division depends only on n. -/
set_option maxHeartbeats 1000000 in
private theorem eventual_formula (rank : ℕ → ℕ → ℕ)
    (hr : ∀ n m, rank n m = n*m*(m+1) ⌈/⌉ (2*m+n-1)) (a m : ℕ) (hm : a ≤ m)
    (cut : a*(a+2)*(a+3) ≤ 2*m+(a+3)-1) :
    rank (a+3) m =
      ((a+3)*(2*m-a)+(if a*(a+2)*(a+3)=0 then 0 else 1)) ⌈/⌉ 4 := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [hr]
  apply short_remainder (by omega) cut
  rw [show 2*(a+v)-a=a+2*v by omega,show 2*(a+v)+(a+3)-1=3*a+2*v+2 by omega]
  ring

set_option maxHeartbeats 1000000 in
private theorem tail_count (rank : ℕ → ℕ → ℕ)
    (hr : ∀ n m, rank n m = n*m*(m+1) ⌈/⌉ (2*m+n-1)) (a m t : ℕ) (hm : a ≤ m)
    (cut : a*(a+2)*(a+3) ≤ 2*m+(a+3)-1) :
    rank (a+3) (m+2*t) = rank (a+3) m + (a+3)*t := by
  rw [eventual_formula rank hr a (m+2*t) (by omega) (by omega),
      eventual_formula rank hr a m hm cut]
  have step : 2*(m+2*t)-a=2*m-a+4*t := by omega
  rw [step,Nat.mul_add,show (a+3)*(4*t)=4*((a+3)*t) by ring]
  simp only [Nat.ceilDiv_eq_add_pred_div]
  omega

set_option maxHeartbeats 1000000 in
private theorem round_step {numerator nextNumerator denominator nextDenominator linearTerm n remainder : ℕ} (hd : 0<denominator) (den : nextDenominator=denominator+4)
    (base : 4*numerator=denominator*linearTerm+remainder) (step : nextNumerator=numerator+n*nextDenominator+linearTerm) :
    nextNumerator ⌈/⌉ nextDenominator ≤ numerator ⌈/⌉ denominator+n := by
  let q := numerator ⌈/⌉ denominator
  have capacity : numerator ≤ denominator*q := (ceilDiv_le_iff_le_mul hd).mp (le_refl q)
  have Lbound : denominator*linearTerm ≤ denominator*(4*q) := calc
    denominator*linearTerm ≤ 4*numerator := by omega
    _ ≤ 4*(denominator*q) := Nat.mul_le_mul_left 4 capacity
    _ = denominator*(4*q) := by ring
  have rounded : linearTerm ≤ 4*q := (mul_le_mul_iff_right₀ hd).mp Lbound
  apply (ceilDiv_le_iff_le_mul (by omega : 0<nextDenominator)).mpr
  change nextNumerator ≤ nextDenominator*(q+n)
  calc
    nextNumerator = numerator+n*nextDenominator+linearTerm := step
    _ ≤ denominator*q+n*nextDenominator+4*q := by omega
    _ = nextDenominator*(q+n) := by rw [den]; ring

set_option maxHeartbeats 1000000 in
private theorem step_le (rank : ℕ → ℕ → ℕ)
    (hr : ∀ n m, rank n m = n*m*(m+1) ⌈/⌉ (2*m+n-1)) (a m : ℕ) (hm : a ≤ m) :
    rank (a+3) (m+2) ≤ rank (a+3) m+(a+3) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [hr (a+3) (a+v+2), hr (a+3) (a+v)]
  rw [show 2*(a+v)+(a+3)-1=3*a+2*v+2 by omega,
      show 2*(a+v+2)+(a+3)-1=(3*a+2*v+2)+4 by omega]
  apply round_step (linearTerm:=(a+3)*(a+2*v)) (remainder:=a*(a+2)*(a+3)) (by omega) rfl <;> ring

set_option maxHeartbeats 1000000 in
private theorem cover (rank : ℕ → ℕ → ℕ)
    (hr : ∀ n m, rank n m=n*m*(m+1) ⌈/⌉ (2*m+n-1)) (Q : ℕ → ℕ → Prop)
    (seeds : ∀ n m, 7 ≤ n → n ≤ m → m ≤ n+(n-3)*(n-1)*n+1 →
      (m=n ∨ m=n+1 ∨ rank n m < rank n (m-2)+n) → Q n m)
    (grow : ∀ n m, 7 ≤ n → n ≤ m → rank n (m+2)=rank n m+n → Q n m → Q n (m+2))
    (n m : ℕ) (hn : 7 ≤ n) (hm : n ≤ m) : Q n m := by
  obtain ⟨a,rfl⟩ : ∃ a, n=a+3 := ⟨n-3,by omega⟩
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases first : m=a+3 ∨ m=a+3+1
    · exact seeds _ _ hn hm (by rcases first with h|h <;> omega) (first.elim Or.inl (fun h => Or.inr (Or.inl h)))
    let p := m-2
    have ep : m=p+2 := by dsimp [p]; omega
    have hp : a+3 ≤ p := by dsimp [p]; omega
    have bound := step_le rank hr a p (by omega)
    rw [← ep] at bound
    by_cases jump : rank (a+3) m < rank (a+3) p+(a+3)
    · apply seeds _ _ hn hm _ (Or.inr (Or.inr jump))
      simp only [show a+3-3=a by omega,show a+3-1=a+2 by omega]
      by_contra late
      have tail := tail_count rank hr a p 1 (by omega) (by omega)
      simp only [Nat.mul_one,← ep] at tail
      omega
    · have old := ih p (by omega) hp
      have regular : rank (a+3) (p+2)=rank (a+3) p+(a+3) := by rw [← ep]; omega
      exact ep ▸ grow _ p hn hp regular old

/-- Check the first two sizes and the later strict changes of the predicted count.
The explicit cutoff makes this part a finite problem for each n. -/
def H1 : Prop :=
  let rank (n m : ℕ) := n*m*(m+1) ⌈/⌉ (2*m+n-1)
  let Q (n m : ℕ) : Prop :=
    let a := n-1
    let b := m-1
    let c := m+1
    let d := rank n m-c
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2))
  ∀ n m : ℕ, 7 ≤ n → n ≤ m → m ≤ n+(n-3)*(n-1)*n+1 →
    (m=n ∨ m=n+1 ∨ rank n m < rank n (m-2)+n) → Q n m

/-- On a regular width-two step, a smaller chart witness implies the larger one. -/
def H2 : Prop :=
  let rank (n m : ℕ) := n*m*(m+1) ⌈/⌉ (2*m+n-1)
  let Q (n m : ℕ) : Prop :=
    let a := n-1
    let b := m-1
    let c := m+1
    let d := rank n m-c
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2))
  ∀ n m : ℕ, 7 ≤ n → n ≤ m → rank n (m+2)=rank n m+n → Q n m → Q n (m+2)

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1.H4 := by
  intro seeds grow
  let rank (n m : ℕ) := n*m*(m+1) ⌈/⌉ (2*m+n-1)
  let Q (n m : ℕ) : Prop :=
    let a := n-1
    let b := m-1
    let c := m+1
    let d := rank n m-c
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2))
  have hit := cover rank (fun _ _ => rfl) Q seeds grow
  intro a b ha hab _
  have proof := hit (a+1) (b+1) (by omega) (by omega)
  have den : 2*(b+1)+(a+1)-1=a+b+(b+2) := by omega
  let chartProp (a b c r : ℕ) : Prop :=
    let d := r-c
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2))
  change chartProp a b (b+2) (rank (a+1) (b+1)) at proof
  have recalc : rank (a+1) (b+1)=(a+1)*(b+1)*(b+2) ⌈/⌉ (a+b+(b+2)) := by
    dsimp only [rank]
    rw [den]
  rw [recalc] at proof
  exact proof

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1_H4_R1
