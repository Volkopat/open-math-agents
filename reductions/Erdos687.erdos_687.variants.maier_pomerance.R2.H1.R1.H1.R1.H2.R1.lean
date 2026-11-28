import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1
import Mathlib


-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2
-- Credit: @carterleffen

/-!
# A finite stopping ledger, uniform count errors, and aligned bins

At nonempty even histories, the stopped reference is exactly the part of the
reference polynomial below the cut. The error estimate applies to any expanded
subfamily. The geometric alternative controls its exceptional reciprocal mass
or exhibits an aligned bin whose actual congruence count is too small.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
open Filter Finset Real
open scoped Classical

def H1 : Prop := ∀ (Y : ℕ) (w z μ : ℝ),
  let P := (Icc (⌊w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
  let Q := (range (⌊w⌋₊+1)).filter Nat.Prime
  let D := fun d : Finset ℕ => ∏ p∈d,(p:ℝ)
  let g := fun d => log (Y/D d)/log w+2-1/100
  let e := fun p : ℕ => log p/log w
  let T := P.powerset.filter fun d => ∀ p∈d,
    let A := d.filter (p ≤ ·)
    Even A.card → max (2*e p) (e p+2) ≤ g A
  ∀ a : ℕ → ℕ,
  let Z := fun d S : Finset ℕ => (Icc 1 Y).filter fun n =>
    (∀ p∈d,n ≡ a p [MOD p]) ∧ ∀ p∈S,¬ (n ≡ a p [MOD p])
  let I := fun u d : Finset ℕ => u⊆d ∧ ∀ p∈u,∀ q∈d\u,q<p
  ∀ F ⊆ T, (∀ d∈F,d.Nonempty ∧ Even d.card ∧ ∀ u∈F,I u d → u=d) →
   let E := T.filter fun d => ∀ u∈F,¬I u d
   (μ*(∑ d∈T\E,(-1:ℝ)^d.card/D d) ≤
   ∑ d∈F, ((Z d (Q ∪ P.filter (fun p => ∀ q∈d,p<q))).card:ℝ)) →
   μ*(∑ d∈T,(-1:ℝ)^d.card/D d) - (∑ d∈E, |((Z d Q).card:ℝ)-μ/D d|) ≤ (((Icc 1 Y).filter fun n => ∀ p ≤ ⌊z⌋₊,p.Prime → ¬ (n ≡ a p [MOD p])).card:ℝ)

def H2 : Prop := ∃ k ε δ : ℝ, 3≤k ∧ 0<ε ∧ 0<δ ∧ ∀ᶠ z : ℝ in atTop,
  let L := log z
  let Y := ⌊z^2/L^2⌋₊
  let w := L/(log L)^2
  let B := L/log w
  let P := (Icc (⌊w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
  let Q := (range (⌊w⌋₊+1)).filter Nat.Prime
  let v := fun S : Finset ℕ => ∏ p∈S,(1-(p:ℝ)⁻¹)
  let μ := Y*v Q
  let D := fun d : Finset ℕ => ∏ p∈d,(p:ℝ)
  let g := fun d => log (Y/D d)/log w+2-1/100
  let e := fun p : ℕ => log p/log w
  let T := P.powerset.filter fun d => ∀ p∈d,
    let A := d.filter (p ≤ ·)
    Even A.card → max (2*e p) (e p+2) ≤ g A
  ∀ a : ℕ → ℕ,
  let Z := fun d S : Finset ℕ => (Icc 1 Y).filter fun n =>
    (∀ p∈d,n ≡ a p [MOD p]) ∧ ∀ p∈S,¬ (n ≡ a p [MOD p])
  ∀ E ⊆ T,
   let A := E.filter fun d => g d≤k ∧ ε < |(Z d Q).card/(μ/D d)-1|
   B^2*(∑ d∈A,(D d)⁻¹)≤δ →
   (∑ d∈E, |((Z d Q).card:ℝ)-μ/D d|) ≤ μ*(1/(100*B^2))

def H3 : Prop := ∀ k ε δ : ℝ, 3≤k → 0<ε → 0<δ → ∀ d : ℝ, 0<d → d≤1/4 → ∀ N : ℕ,
 ∃ C : ℝ, 0≤C ∧ ∀ K : ℝ, 0<K → ∃ b x : ℝ, 1<b ∧ 0<x ∧ ∀ W : ℝ, ∀ᶠ z : ℝ in atTop,
  let L := log z
  let Y := ⌊z^2/L^2⌋₊
  let w := L/(log L)^2
  let B := L/log w
  let P := (Icc (⌊w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
  let Q := (range (⌊w⌋₊+1)).filter Nat.Prime
  let v := fun S : Finset ℕ => ∏ p∈S,(1-(p:ℝ)⁻¹)
  let μ := Y*v Q
  let D := fun d : Finset ℕ => ∏ p∈d,(p:ℝ)
  let g := fun d => log (Y/D d)/log w+2-1/100
  let e := fun p : ℕ => log p/log w
  let T := P.powerset.filter fun d => ∀ p∈d,
    let A := d.filter (p ≤ ·)
    Even A.card → max (2*e p) (e p+2) ≤ g A
  ∀ a : ℕ → ℕ,
  let Z := fun d S : Finset ℕ => (Icc 1 Y).filter fun n =>
    (∀ p∈d,n ≡ a p [MOD p]) ∧ ∀ p∈S,¬ (n ≡ a p [MOD p])
  let I := fun u d : Finset ℕ => u⊆d ∧ ∀ p∈u,∀ q∈d\u,q<p
  (∃ F ⊆ T, (∀ d∈F, d.Nonempty ∧ Even d.card ∧ ∀ u∈F,I u d → u=d) ∧
   let E := T.filter fun d => ∀ u∈F,¬I u d
   let A := E.filter fun d => g d≤k ∧ ε < |(Z d Q).card/(μ/D d)-1|
   B^2*(∑ d∈A,(D d)⁻¹)≤δ ∧
   μ*(∑ d∈T\E,(-1:ℝ)^d.card/D d) ≤
   ∑ d∈F, ((Z d (Q ∪ P.filter (fun p => ∀ q∈d,p<q))).card:ℝ)) ∨ ∃ (m q : ℕ) (s t : ℝ) (r : ℚ),
   let J := Nat.primesLE ⌊(1+t)*s⌋₊ \ Nat.primesLE ⌊s⌋₊
   let A := fun p : ℕ => (r.den:ZMod p)*(a p:ZMod p)=(r.num:ZMod p)
   let G := J.filter A
   let h := m.Prime ∧ N ≤ m ∧ exp (K*(log w)^3) ≤ m ∧
    (m:ℝ)≤exp (b*K*(log w)^3) ∧ exp (w^((1:ℝ)/4)*log w) ≤ s ∧ x/4 ≤ t ∧ t≤1 ∧
    0<Y ∧ 0<q ∧ (r.den:ℝ)≤w^C ∧ |(r.num:ℝ)|≤Y*w^(C+2) ∧
    (∀ u∈Set.Icc s ((1+t)*s),log (Y/(u*q))/log m ∈ Set.Icc (203/100) (219/100)) ∧
    (∀ u∈q.primeFactors,m ≤ u ∧ A u) ∧
    (∀ p∈J,m ≤ p ∧ Squarefree (p*q) ∧ r.den.Coprime p) ∧ (1-d)*(J.card:ℝ)≤G.card
   W≤w ∧ h ∧ (∑ p∈G,((Z (p*q).primeFactors ((range m).filter Nat.Prime)).card:ℝ)) <
    (33/100*v (Nat.primesLE m))*(∑ p∈G,(Y:ℝ)/((p:ℝ)*q))

def H4 : Prop := ∃ d : ℝ, 0<d ∧ d≤1/4 ∧ ∃ N : ℕ, ∀ C : ℝ, 0≤C → ∃ K : ℝ, 0<K ∧
 ∀ b x : ℝ, 1<b → 0<x → ∃ W : ℝ, ∀ w : ℝ, W≤w → ∀ (Y : ℕ) (a : ℕ → ℕ)
 (m q : ℕ) (s t : ℝ) (r : ℚ),
   let v := fun S : Finset ℕ => ∏ p∈S,(1-(p:ℝ)⁻¹)
   let Z := fun d S : Finset ℕ => (Icc 1 Y).filter fun n =>
    (∀ p∈d,n ≡ a p [MOD p]) ∧ ∀ p∈S,¬ (n ≡ a p [MOD p])
   let J := Nat.primesLE ⌊(1+t)*s⌋₊ \ Nat.primesLE ⌊s⌋₊
   let A := fun p : ℕ => (r.den:ZMod p)*(a p:ZMod p)=(r.num:ZMod p)
   let G := J.filter A
   let h := m.Prime ∧ N ≤ m ∧ exp (K*(log w)^3) ≤ m ∧
    (m:ℝ)≤exp (b*K*(log w)^3) ∧ exp (w^((1:ℝ)/4)*log w) ≤ s ∧ x/4 ≤ t ∧ t≤1 ∧
    0<Y ∧ 0<q ∧ (r.den:ℝ)≤w^C ∧ |(r.num:ℝ)|≤Y*w^(C+2) ∧
    (∀ u∈Set.Icc s ((1+t)*s),log (Y/(u*q))/log m ∈ Set.Icc (203/100) (219/100)) ∧
    (∀ u∈q.primeFactors,m ≤ u ∧ A u) ∧
    (∀ p∈J,m ≤ p ∧ Squarefree (p*q) ∧ r.den.Coprime p) ∧ (1-d)*(J.card:ℝ)≤G.card
   h → (33/100*v (Nat.primesLE m))*(∑ p∈G,(Y:ℝ)/((p:ℝ)*q)) ≤
    ∑ p∈G,((Z (p*q).primeFactors ((range m).filter Nat.Prime)).card:ℝ)

lemma real_prefix (d : Finset ℕ) (p : ℕ) :
    (d >>= fun n => pure (n:ℝ)).filter ((p:ℝ) ≤ ·) =
    (d.filter (p ≤ ·)).image (fun n : ℕ => (n:ℝ)) := by
  ext y
  simp
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, h⟩
    exact ⟨n, ⟨hn, by exact_mod_cast h⟩, rfl⟩
  · rintro ⟨n, ⟨hn, hp⟩, rfl⟩
    exact ⟨⟨n, hn, rfl⟩, by exact_mod_cast hp⟩

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1.H2 := by
  intro ledger errors geometry arithmetic
  obtain ⟨k, ε, δ, hk, hε, hδ, errors⟩ := errors
  obtain ⟨d, hd, hd', N, localBound⟩ := arithmetic
  obtain ⟨C, hC, transfer⟩ := geometry k ε δ hk hε hδ d hd hd' N
  obtain ⟨K, hK, localBound⟩ := localBound C hC
  obtain ⟨b, x, hb, hx, transfer⟩ := transfer K hK
  obtain ⟨W, localBound⟩ := localBound b x hb hx
  filter_upwards [transfer W, errors] with z hz he
  dsimp only
  intro a
  let L := Real.log z
  let Y := ⌊z^2/L^2⌋₊
  let w := L/(Real.log L)^2
  let B := L/log w
  let Q := (range (⌊w⌋₊+1)).filter Nat.Prime
  let μ : ℝ := (Y:ℝ)*(∏ p∈Q,(1-(p:ℝ)⁻¹))
  rcases hz a with ⟨F,hF,ha,hcost,hstop⟩ | ⟨m,q,s,t,r,hw,hh,hbad⟩
  · have hL := ledger Y w z μ a F hF ha hstop
    have hc := he a _ (Finset.filter_subset _ _) hcost
    apply le_trans _ hL
    rw [mul_sub]
    simp only [real_prefix, Finset.card_image_of_injective _ (Nat.cast_injective (R:=ℝ)),
      Finset.prod_image (Nat.cast_injective (R:=ℝ)).injOn]
    exact sub_le_sub_left hc _
  · exact False.elim ((not_lt_of_ge (localBound w hw Y a m q s t r hh)) hbad)
end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
