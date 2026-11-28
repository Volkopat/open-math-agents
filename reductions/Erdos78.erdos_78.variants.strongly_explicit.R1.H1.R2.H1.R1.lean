import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2

/-!
A deterministic constant-factor comparison of two tuple counts suffices for
uniform range avoidance. At each output prefix, let c and d be the numbers
of preimages in its children. Counts of ordered k-tuples are c^k and d^k.
Even a factor-four error in picking the lighter tuple bucket still decreases
the preimage mass fast enough when k = 2*A^2+1, where the stretch is A and
the output length is A^3. The prefix walk makes exactly A^3 adaptive queries.
-/

namespace OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2_H1_R1

open Finset Filter ComplexityTheory

/-- Deterministically compare the two polynomial-length tuple populations
at each dyadic split, up to a factor of four. Ordinary factor-two estimates
of both counts suffice by choosing the smaller estimate. -/
def H1 : Prop := ∀ f : ℕ × ℕ → ℕ, IsPolyTime f → ∀ p : Polynomial ℕ,
  ∃ b : ℕ × ℕ × ℕ → Bool, IsPolyTime b ∧ ∀ᶠ n : ℕ in atTop,
    let A := p.eval n + 1
    let B := 2^(A^3-A)
    let k := 2*A^2+1
    ∀ h < A^3, ∀ j : ℕ,
      let q := b (2^n,h,j)
      let count := fun (v : Bool) =>
        ((range B).filter fun x => f (2^n,x) / 2^h = 2*j+Bool.toNat v).card
      (count q)^k ≤ 4*(count (!q))^k

/-- Closure under a polynomial-length loop appending oracle bits. The loop
counter and every prefix have polynomial bit length in the original input. -/
def H2 : Prop := ∀ (b : ℕ × ℕ × ℕ → Bool) (p : Polynomial ℕ), IsPolyTime b →
  IsPolyTime (fun t : ℕ =>
    Nat.rec (motive := fun _ => ℕ → ℕ) id
      (fun h prev j => prev (2*j+Bool.toNat (b (t,h,j)))) ((p.eval t.log2+1)^3) 0)

theorem main : H1 → H2 → OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2.H1 := by
  let bucket := fun (f : ℕ × ℕ → ℕ) (t B h j : ℕ) =>
    (range B).filter fun x => f (t,x) / 2^h = j
  let child := fun (v : Bool) (j : ℕ) => 2*j+v.toNat
  let walk := fun (b : ℕ × ℕ × ℕ → Bool) (t h j : ℕ) =>
    Nat.rec (motive := fun _ => ℕ → ℕ) id
      (fun r prev j₀ => prev (child (b (t,r,j₀)) j₀)) h j

  have children_le (f : ℕ × ℕ → ℕ) (t B h j : ℕ) (q : Bool) :
      (bucket f t B h (child q j)).card + (bucket f t B h (child (!q) j)).card ≤
      (bucket f t B (h+1) j).card := by
    let left := bucket f t B h (2*j)
    let right := bucket f t B h (2*j+1)
    have dis : Disjoint left right := by
      apply disjoint_left.mpr
      intro x hx hy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      change f (t,x)/2^h=2*j at hx'
      change f (t,x)/2^h=2*j+1 at hy'
      omega
    have sub : left ∪ right ⊆ bucket f t B (h+1) j := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      all_goals
        obtain ⟨hm,he⟩ := mem_filter.mp hx
        apply mem_filter.mpr
        refine ⟨hm,?_⟩
        rw [pow_succ,← Nat.div_div_eq_div_mul]
      · change f (t,x)/2^h=2*j at he; omega
      · change f (t,x)/2^h=2*j+1 at he; omega
    have hh := card_le_card sub
    rw [card_union_of_disjoint dis] at hh
    cases q <;> simpa [left,right,child,add_comm] using hh

  have local_bound {c d m k : ℕ} (hpop : c+d ≤ m) (hcmp : c^k ≤ 4*d^k) :
      (2*c)^k ≤ 4*m^k := by
    rcases le_total c d with h | h
    · have hhalf := Nat.pow_le_pow_left (show 2*c ≤ m by omega) k
      omega
    · have hhalf := Nat.pow_le_pow_left (show 2*d ≤ m by omega) k
      calc (2*c)^k = 2^k*c^k := mul_pow ..
           _ ≤ 2^k*(4*d^k) := Nat.mul_le_mul_left _ hcmp
           _ = 4*(2*d)^k := by rw [mul_pow]; ring
           _ ≤ 4*m^k := Nat.mul_le_mul_left _ hhalf

  have path_bound (f : ℕ × ℕ → ℕ) (b : ℕ × ℕ × ℕ → Bool) (t B L k : ℕ)
      (cmp : ∀ h<L, ∀ j, let q := b (t,h,j)
        (bucket f t B h (child q j)).card^k ≤ 4*(bucket f t B h (child (!q) j)).card^k) :
      ∀ h≤L, ∀ j, (2^h*(bucket f t B 0 (walk b t h j)).card)^k ≤
        4^h*(bucket f t B h j).card^k := by
    intro h
    induction h with
    | zero => simp [walk]
    | succ h ih =>
      intro hh j
      let q := b (t,h,j)
      let c := (bucket f t B h (child q j)).card
      let m := (bucket f t B (h+1) j).card
      let z := (bucket f t B 0 (walk b t h (child q j))).card
      have localStep : (2*c)^k ≤ 4*m^k :=
        local_bound (children_le f t B h j q) (cmp h (by omega) j)
      have prev : (2^h*z)^k ≤ 4^h*c^k := ih (by omega) (child q j)
      change (2^(h+1)*z)^k ≤ 4^(h+1)*m^k
      calc (2^(h+1)*z)^k = 2^k*(2^h*z)^k := by rw [← mul_pow,pow_succ]; ring
           _ ≤ 2^k*(4^h*c^k) := Nat.mul_le_mul_left _ prev
           _ = 4^h*(2*c)^k := by rw [mul_pow]; ring
           _ ≤ 4^h*(4*m^k) := Nat.mul_le_mul_left _ localStep
           _ = 4^(h+1)*m^k := by rw [pow_succ]; ring

  have walk_lt (b : ℕ × ℕ × ℕ → Bool) (t h j : ℕ) :
      walk b t h j < (j+1)*2^h := by
    induction h generalizing j with
    | zero => simp [walk]
    | succ h ih =>
      let q := b (t,h,j)
      have hc : child q j + 1 ≤ 2*(j+1) := by cases q <;> simp [child] <;> omega
      exact (ih (child q j)).trans_le ((Nat.mul_le_mul_right (2^h) hc).trans_eq
        (by rw [pow_succ]; ring))

  have empty_leaf {A z : ℕ} (ha : 0<A)
      (bound : (2^(A^3)*z)^(2*A^2+1) ≤ 4^(A^3)*(2^(A^3-A))^(2*A^2+1)) : z=0 := by
    let L := A^3
    let k := 2*A^2+1
    by_contra hz
    have hpos : 1≤z := Nat.pos_of_ne_zero hz
    have hmul : 2^L ≤ 2^L*z := by simpa using Nat.mul_le_mul_left (2^L) hpos
    have he : (2^L)^k ≤ 4^L*(2^(L-A))^k := (Nat.pow_le_pow_left hmul k).trans bound
    rw [← pow_mul, show (4:ℕ)=2^2 by decide, ← pow_mul, ← pow_mul, ← pow_add] at he
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp he
    have hAL : A ≤ L := Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) A
    have hs : (L-A)*k+A*k=L*k := by rw [← add_mul,Nat.sub_add_cancel hAL]
    have hgap : 2*L < A*k := by dsimp [L,k]; nlinarith
    omega

  intro approx loop f hf p
  obtain ⟨b,hb,ev⟩ := approx f hf p
  refine ⟨_,loop b p hb,?_⟩
  filter_upwards [ev] with n cmp
  rw [Nat.log2_two_pow]
  let A := p.eval n + 1
  let L := A^3
  let k := 2*A^2+1
  let B := 2^(L-A)
  let y := walk b (2^n) L 0
  have path := path_bound f b (2^n) B L k cmp L le_rfl 0
  have root : (bucket f (2^n) B L 0).card ≤ B :=
    (card_filter_le ..).trans_eq (card_range _)
  have mult := Nat.mul_le_mul_left (4^L) (Nat.pow_le_pow_left root k)
  have zero : (bucket f (2^n) B 0 y).card=0 := empty_leaf (Nat.succ_pos _) (path.trans mult)
  refine ⟨by simpa [y] using walk_lt b (2^n) L 0,?_⟩
  intro x hx he
  have hit : x∈bucket f (2^n) B 0 y := by
    simp only [bucket, pow_zero, Nat.div_one, mem_filter, mem_range]
    exact ⟨hx,he⟩
  have := Finset.card_pos.mpr ⟨x,hit⟩
  omega

end OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2_H1_R1
