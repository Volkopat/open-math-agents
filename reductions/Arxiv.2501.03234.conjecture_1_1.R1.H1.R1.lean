import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1
import Mathlib.GroupTheory.OrderOfElement

/-!
Index the nonzero residues by powers of a generator. Their parity bits
form a cyclic word w. The theta sum is four times the number of ordered
pairs of ones whose cyclic sum is another one, minus twice the square of
the number of ones. This replaces a triangular array of floor divisions
with a cyclic convolution.

Packing the word in base B and multiplying by its reversal converts the
convolution into two digits of a single product. Each coefficient counts
at most n² pairs, so B = 2^34 prevents carries throughout this range.
-/

namespace OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1

open Finset

/-- Carry-free extraction of the cyclic triple correlation of a binary word. -/
def H1 : Prop := ∀ (n B : ℕ) (w : ℕ → ℕ), 0<n → n^2<B → (∀ i<n, w i≤1) →
  let A := ∑ i ∈ range n, w i * B^i
  let R := ∑ i ∈ range n, w i * B^(n-1-i)
  let P := A^2 * R
  (∑ i ∈ range n, ∑ j ∈ range n, w i*w j*w ((i+j)%n)) =
    (P/B^(n-1))%B + (P/B^(2*n-1))%B

/-- The finite test uses only parities of successive powers and a product of
packed integers. The generator can be chosen separately for each prime. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 2<p → p<100000 →
  ∃ (g : (ZMod p)ˣ) (B : ℕ), orderOf g=p-1 ∧ (p-1)^2<B ∧
    let n := p-1
    let w (i : ℕ) := ((↑(g^i) : ZMod p).val)%2
    let A := ∑ i ∈ range n, w i * B^i
    let R := ∑ i ∈ range n, w i * B^(n-1-i)
    let P := A^2 * R
    (∑ i ∈ range n, w i)^2 < 2*((P/B^(n-1))%B + (P/B^(2*n-1))%B)

section Proof

private theorem reindex {α β γ : Type} [DecidableEq β] [AddCommMonoid γ]
    (S : Finset α) (T : Finset β) (v : α → β) (hc : S.card = T.card)
    (hm : ∀ x ∈ S, v x ∈ T) (hi : Set.InjOn v (S:Set α)) (F : β → γ) :
    (∑ y ∈ T,F y) = ∑ x ∈ S,F (v x) := by
  have h : S.image v = T := eq_of_subset_of_card_le (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact hm x hx)
    (by rw [card_image_of_injOn hi,hc])
  rw [← h,sum_image hi]

private theorem baseline (p a : ℕ) (hp : p.Prime) (hodd : Odd p) (ha : a ∈ Ico 1 p) :
    (∑ j ∈ Ico 1 p, (-1:ℤ)^((a*j)%p)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have ha0 : (a:ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact (Nat.not_le_of_lt (mem_Ico.mp ha).2) (Nat.le_of_dvd (mem_Ico.mp ha).1 h)
  have hm (j : ℕ) (hj : j ∈ Ico 1 p) : (a*j)%p ∈ Ico 1 p := by
    refine mem_Ico.mpr ⟨?_,Nat.mod_lt _ hp.pos⟩
    apply Nat.pos_of_ne_zero
    intro hz
    rcases hp.dvd_mul.mp (Nat.dvd_of_mod_eq_zero hz) with h | h
    · exact ha0 ((ZMod.natCast_eq_zero_iff a p).mpr h)
    · exact (Nat.not_le_of_lt (mem_Ico.mp hj).2) (Nat.le_of_dvd (mem_Ico.mp hj).1 h)
  have hi : Set.InjOn (fun j => (a*j)%p) (Ico 1 p : Finset ℕ) := by
    intro i hi j hj he
    have hm' : (a:ZMod p)*(i:ZMod p) = (a:ZMod p)*(j:ZMod p) := by
      apply (ZMod.val_injective p)
      rw [← Nat.cast_mul,← Nat.cast_mul,ZMod.val_natCast,ZMod.val_natCast]
      exact he
    have he' := congrArg ZMod.val (mul_left_cancel₀ ha0 hm')
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_Ico.mp hi).2,
      Nat.mod_eq_of_lt (mem_Ico.mp hj).2] using he'
  rw [← reindex (Ico 1 p) (Ico 1 p) _ rfl hm hi (fun i => (-1:ℤ)^i)]
  obtain ⟨n,hn⟩ := hodd
  have he := OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.alt_sum_zero n
  have hs : p=2*n+1 := by omega
  rw [← hs] at he
  have hneg : (∑ a ∈ Ico 1 p,(-1:ℤ)^a) = -(∑ a ∈ Ico 1 p,(-1:ℤ)^(a-1)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro a ha
    conv_lhs => rw [← Nat.sub_add_cancel (mem_Ico.mp ha).1,pow_succ]
    ring
  omega

private theorem sign_formula (a j p : ℕ) (hp : Odd p) :
    (-1:ℤ)^(a*j/p) = (-1:ℤ)^((a*j)%p) +
      4*((a%2)*(j%2)*(((a*j)%p)%2):ℕ) - 2*((a%2)*(j%2):ℕ) := by
  have h := congrArg (· % 2) (Nat.div_add_mod (a*j) p)
  have hmod : p % 2 = 1 := Nat.odd_iff.mp hp
  simp only [Nat.add_mod, Nat.mul_mod, hmod, one_mul, Nat.mod_mod] at h
  rw [neg_one_pow_eq_pow_mod_two (a*j/p),neg_one_pow_eq_pow_mod_two ((a*j)%p)]
  have split (v : ℕ) : v%2=0 ∨ v%2=1 := by omega
  rcases split a with ha|ha <;> rcases split j with hj|hj <;>
    rcases split (a*j/p) with hk|hk <;> rcases split ((a*j)%p) with hr|hr <;>
    first | (exfalso; norm_num [ha,hj,hk,hr] at h; done) | norm_num [ha,hj,hk,hr]

theorem main : H1 → H2 → OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.H1 := by
  intro pack cert p hp h2p hsmall
  obtain ⟨g,B,horder,hB,hcert⟩ := cert p hp h2p hsmall
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let n := p-1
  let J := Ico 1 p
  let v (i : ℕ) := (↑(g^i) : ZMod p).val
  let w (i : ℕ) := v i % 2
  have hv (i : ℕ) : v i ∈ J := by
    refine mem_Ico.mpr ⟨Nat.pos_of_ne_zero ?_,ZMod.val_lt _⟩
    intro h
    have he : (↑(g^i) : ZMod p) = 0 := by
      apply ZMod.val_injective p
      simpa [v] using h
    exact Units.ne_zero _ he
  have hi : Set.InjOn v (range n : Finset ℕ) := by
    intro i hi j hj he
    apply pow_injOn_Iio_orderOf (x:=g) (by simpa [horder,n] using mem_range.mp hi)
      (by simpa [horder,n] using mem_range.mp hj)
    exact Units.ext (ZMod.val_injective p he)
  have enum (F : ℕ → ℤ) : (∑ a ∈ J,F a) = ∑ i ∈ range n,F (v i) :=
    reindex _ _ _ (by simp [J,n]) (fun i _ => hv i) hi F
  have prodVal (i j : ℕ) : (v i*v j)%p = v ((i+j)%n) := by
    dsimp only [v,n]
    rw [← horder,pow_mod_orderOf,pow_add,Units.val_mul,ZMod.val_mul]
  have ho := hp.odd_of_ne_two (by omega)
  have row (i : ℕ) : (∑ j ∈ range n,(-1:ℤ)^((v i*v j)%p))=0 := by
    rw [← enum (fun t => (-1:ℤ)^((v i*t)%p))]
    exact baseline p (v i) hp ho (hv i)
  let T := ∑ i ∈ range n,∑ j ∈ range n,w i*w j*w ((i+j)%n)
  let N := ∑ i ∈ range n,w i
  have exactSum : Arxiv.«2501.03234».S p = 4*(T:ℤ)-2*(N:ℤ)^2 := by
    rw [OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.S_eq p hp]
    change (∑ a ∈ J,∑ j ∈ J,(-1:ℤ)^(a*j/p)) = _
    rw [enum]
    calc
      _ = ∑ i ∈ range n, ∑ j ∈ range n,
            ((-1:ℤ)^((v i*v j)%p) + 4*(w i*w j*w ((i+j)%n):ℕ) - 2*(w i*w j:ℕ)) := by
          apply sum_congr rfl; intro i _
          rw [enum]
          apply sum_congr rfl; intro j _
          simpa only [w,← prodVal] using sign_formula (v i) (v j) p ho
      _ = _ := by
          dsimp only [T,N]
          push_cast
          simp only [sum_sub_distrib,sum_add_distrib,row,zero_add,← mul_sum,← sum_mul,pow_two]
  have hpck := pack n B w (by dsimp [n]; omega) hB (fun i _ => by dsimp [w]; omega)
  change N^2 < 2*_ at hcert
  change T = _ at hpck
  have ht : N^2 < 2*T := by simpa only [hpck] using hcert
  have hz : (N:ℤ)^2 < 2*(T:ℤ) := by exact_mod_cast ht
  rw [← OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.S_eq_T p hp ho,exactSum]
  linarith

end Proof

end OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1
