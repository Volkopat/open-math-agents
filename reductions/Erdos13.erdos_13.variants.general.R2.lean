import FormalConjectures.ErdosProblems.«13»

/-! Reduction by simultaneous induction on truncated sets of multiples.
The first step collects the established arity and terminal-interval bounds.
The next two steps force residue proportions modulo four and bound the odd count.
The final step concerns only sets satisfying every one of the dilation inequalities. -/
-- Credit: @jenil-bodhani
namespace OMA.R_Erdos13_erdos_13_variants_general_R2
open Finset
open scoped Classical

/-- Previously established range and terminal conditions on any sufficiently large excess. -/
def H1 : Prop := ∀ r : ℕ, ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) → (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m+K < A.card → 3 ≤ r ∧ r < 2^(2^102 : ℕ) ∧ 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m ∧ (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m

/-- Both odd classes occur with positive proportion in a sparse ternary set with many odd members. -/
def H2 : Prop := ∃ W D : ℕ, ∀ (m c : ℕ) (A : Finset ℕ), A ⊆ Icc 1 (4*m) → (∀ a ∈ A, ∀ b : Fin 3 → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (3*m) (4*m) ∩ A).card ≤ m → 4*(Ioc (3*m) (4*m) ∩ A).card ≤ 2*m →
    m ≤ 2*(A.filter (fun x => x%2=1)).card+1 → m ≤ W*(A.filter (fun x => x%2=1 ∧ x%4≠c)).card+D ∧
    m ≤ W*(A.filter (fun x => x%4=2)).card+D ∧ m ≤ W*(A.filter (fun x => x%4=0)).card+D ∧
    5668752120000*(A.filter (fun x => x%2=1)).card+m ≤ 3779168080000*m+D

/-- The same residue conclusion for every arity at least four. -/
def H3 : Prop := ∀ r : ℕ, 4 ≤ r → ∃ W D : ℕ, ∀ (m c : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) → (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m ≤ 2*(A.filter (fun x => x%2=1)).card+1 → m ≤ W*(A.filter (fun x => x%2=1 ∧ x%4≠c)).card+D ∧
    m ≤ W*(A.filter (fun x => x%4=2)).card+D ∧
    (32 ≤ r → 100*(A.filter (fun x => x%2=1)).card ≤ 68*m+D)

/-- The witness estimate with uniform conditions on divisibility and on the two odd residues. -/
def H4 : Prop := ∀ r : ℕ, 3 ≤ r → r < 2^(2^102 : ℕ) → ∀ W D : ℕ, ∃ K : ℕ,
    ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) → (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    (∀ d t : ℕ, 0 < d → t < m → m < t + (A.filter (fun x => ¬(d ∣ x ∧ x ≤ d*((r+1)*t)))).card) → m ≤ 2*(A.filter (fun x => x%2=1)).card+1 → (∀ c : ℕ, m ≤ W*(A.filter (fun x => x%2=1 ∧ x%4≠c)).card+D) →
    m ≤ W*(A.filter (fun x => x%4=2)).card+D →
    (r = 3 → m ≤ W*(A.filter (fun x => x%4=0)).card+D ∧
      5668752120000*(A.filter (fun x => x%2=1)).card+m ≤ 3779168080000*m+D) →
    (32 ≤ r → 100*(A.filter (fun x => x%2=1)).card ≤ 68*m+D) → A.card ≤ m+K

lemma normalize {r g N : ℕ} (gp : 0<g) (A : Finset ℕ) (sub : A⊆Icc 1 N)
    (div : ∀ x∈A,g∣x) (free : (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i)) :
    ∃ B : Finset ℕ, B⊆Icc 1 (N/g) ∧ (∀ a ∈ B, ∀ b : Fin r → ℕ, (∀ i, b i ∈ B) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) ∧ A.card ≤ B.card ∧ ∀ x∈B,g*x∈A := by
  let B := (Icc 1 (N/g)).filter (fun x => g*x∈A)
  have mem (x) (hx : x∈B) := (mem_filter.mp hx).2
  refine ⟨B,filter_subset _ _,?_,?_,mem⟩
  · intro a ha b hb hlt dv
    apply free (g*a) (mem a ha) (fun i => g*b i) (fun i => mem _ (hb i))
      (fun i => Nat.mul_lt_mul_of_pos_left (hlt i) gp)
    obtain ⟨k,eq⟩ := dv
    exact ⟨k,by rw [←mul_sum,eq,Nat.mul_assoc]⟩
  · apply card_le_card_of_injOn (fun x => x/g)
    · intro x hx
      change x∈A at hx
      have eq := Nat.mul_div_cancel' (div x hx)
      have bounds := mem_Icc.mp (sub hx)
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨?_,Nat.div_le_div_right bounds.2⟩,by change g*(x/g)∈A; rwa [eq]⟩
      apply Nat.pos_of_ne_zero
      intro zero
      change x/g=0 at zero
      rw [zero,Nat.mul_zero] at eq
      omega
    · intro x hx y hy he
      exact (Nat.mul_div_cancel' (div x hx)).symm.trans
        ((congrArg (g*·) he).trans (Nat.mul_div_cancel' (div y hy)))


lemma critical_half {r m : ℕ} (hm : 2≤ m) (A : Finset ℕ) (fit : A⊆Icc 1 ((r+1)*m))
    (rec : (∀ d t : ℕ, 0 < d → t < m → m < t + (A.filter (fun x => ¬(d ∣ x ∧ x ≤ d*((r+1)*t)))).card)) : m≤2*(A.filter (fun x=>x%2=1)).card+1 := by
  let n:=(m+1)/2
  have up : (r+1)*m≤2*((r+1)*n) := by
    have h:=Nat.mul_le_mul_left (r+1) (show m≤2*n by dsimp [n];omega)
    nlinarith only [h]
  have h:=rec 2 n (by decide) (by dsimp [n];omega)
  have eq : A.filter (fun x=>¬(2∣x ∧ x≤2*((r+1)*n)))=A.filter (fun x=>x%2=1) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx,h⟩
      have le:=(mem_Icc.mp (fit hx)).2.trans up
      exact ⟨hx,by omega⟩
    · rintro ⟨hx,h⟩
      exact ⟨hx,by omega⟩
  rw [eq] at h
  dsimp [n] at h
  omega


theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos13.erdos_13.variants.general := by
  classical
  intro screen ternary higher finish r
  unfold H1 at screen
  unfold H4 at finish
  generalize (2^(2^102 : ℕ)) = cutoff at screen finish
  obtain ⟨J,gate⟩:=screen r
  by_cases range : 3≤r ∧ r<cutoff
  swap
  · refine ⟨(J+1 : ℕ),?_⟩
    intro N A sub free
    let m:=N/(r+1)+1
    have up:=Nat.lt_mul_div_succ N (show 0<r+1 by omega)
    change N<(r+1)*m at up
    have bound : A.card≤ m+J := by
      by_contra! bad
      have h:=gate m A (sub.trans (Icc_subset_Icc_right up.le)) free bad
      exact range ⟨h.1,h.2.1⟩
    have n:=Nat.div_mul_le_self N (r+1)
    have b:=Nat.mul_le_mul_right (r+1) bound
    dsimp only [m] at b
    have num : A.card*(r+1)≤N+(J+1)*(r+1) := by nlinarith only [b,n]
    have realnum : (A.card:ℝ)*((r:ℝ)+1)≤(N:ℝ)+((J:ℝ)+1)*((r:ℝ)+1):=by exact_mod_cast num
    push_cast
    rw [←sub_le_iff_le_add,le_div_iff₀ (by positivity)]
    linarith only [realnum]
  have classes : ∃ W D : ℕ, ∀ (m c : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) → (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m ≤ 2*(A.filter (fun x => x%2=1)).card+1 → m ≤ W*(A.filter (fun x => x%2=1 ∧ x%4≠c)).card+D ∧
    m ≤ W*(A.filter (fun x => x%4=2)).card+D ∧
    (r=3 → m ≤ W*(A.filter (fun x=>x%4=0)).card+D ∧
       5668752120000*(A.filter (fun x=>x%2=1)).card+m ≤ 3779168080000*m+D) ∧
    (32≤r → 100*(A.filter (fun x=>x%2=1)).card≤68*m+D) := by
    rcases range.1.eq_or_lt with eq|hi
    · subst r
      obtain ⟨W,D,hit⟩:=ternary
      refine ⟨W,D,?_⟩
      intro m c A sub free big sp top half
      obtain ⟨odd,two,zero,frac⟩:=hit m c A sub free big sp top half
      exact ⟨odd,two,fun _=>⟨zero,frac⟩,by omega⟩
    · obtain ⟨W,D,hit⟩:=higher r hi
      refine ⟨W,D,?_⟩
      intro m c A sub free big sp top half
      obtain ⟨odd,two,frac⟩:=hit m c A sub free big sp top half
      exact ⟨odd,two,by omega,frac⟩
  obtain ⟨W,D,both⟩:=classes
  obtain ⟨K,done⟩:=finish r range.1 range.2 W D
  let C:=J+K+r+2
  have aligned (m : ℕ) : ∀ A : Finset ℕ, A ⊆ Icc 1 ((r+1)*m) → (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) → A.card≤ m+C := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro A sub free
      by_contra! large
      have excess : m+J<A.card := by dsimp [C] at large;omega
      have g:=gate m A sub free excess
      have ct:=card_le_card sub
      simp only [Nat.card_Icc,Nat.add_one_sub_one] at ct
      have mp : 2≤ m := by
        by_contra! bad
        have h:=Nat.mul_le_mul_left (r+1) (show m≤1 by omega)
        dsimp [C] at large;omega
      by_cases record : (∀ d t : ℕ, 0 < d → t < m → m < t + (A.filter (fun x => ¬(d ∣ x ∧ x ≤ d*((r+1)*t)))).card)
      · have half:=critical_half mp A sub record
        have each (c : ℕ):=both m c A sub free (show m≤A.card by omega) g.2.2.1 g.2.2.2 half
        have bound:=done m A sub free (by omega) g.2.2.1 g.2.2.2 record half
          (fun c=>(each c).1) (each 0).2.1 (each 0).2.2.1 (each 0).2.2.2
        dsimp [C] at large;omega
      simp only [not_forall,not_lt] at record
      obtain ⟨d,t,dp,tm,short⟩:=record
      let P:=fun x : ℕ=>d∣x ∧ x≤d*((r+1)*t)
      let B:=A.filter P
      have inc : B⊆A:=filter_subset _ _
      have fit : B⊆Icc 1 (d*((r+1)*t)):=fun x hx=>
        mem_Icc.mpr ⟨(mem_Icc.mp (sub (inc hx))).1,(mem_filter.mp hx).2.2⟩
      obtain ⟨S,fit,clean,area,_⟩:=normalize (r:=r) dp B fit (fun x hx=>(mem_filter.mp hx).2.1)
        (fun a ha b hb=>free a (inc ha) b (fun i=>inc (hb i)))
      rw [Nat.mul_div_cancel_left _ dp] at fit
      have bound:=ih t tm S fit clean
      have part:=A.card_filter_add_card_filter_not P
      change B.card+(A.filter (fun x=>¬P x)).card=A.card at part
      change t+(A.filter (fun x=>¬P x)).card≤ m at short
      omega
  refine ⟨(C+1 : ℕ),?_⟩
  intro N A sub free
  let m:=N/(r+1)+1
  have up:=Nat.lt_mul_div_succ N (show 0<r+1 by omega)
  change N<(r+1)*m at up
  have bound:=aligned m A (sub.trans (Icc_subset_Icc_right up.le)) free
  have n:=Nat.div_mul_le_self N (r+1)
  have b:=Nat.mul_le_mul_right (r+1) bound
  dsimp only [m] at b
  have num : A.card*(r+1)≤N+(C+1)*(r+1) := by nlinarith only [b,n]
  have realnum : (A.card:ℝ)*((r:ℝ)+1)≤(N:ℝ)+((C:ℝ)+1)*((r:ℝ)+1):=by exact_mod_cast num
  push_cast
  rw [←sub_le_iff_le_add,le_div_iff₀ (by positivity)]
  linarith only [realnum]

end OMA.R_Erdos13_erdos_13_variants_general_R2
