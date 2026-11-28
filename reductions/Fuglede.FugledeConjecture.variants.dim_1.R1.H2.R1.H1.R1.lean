import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1

/-!
A common spectrum for a three-point fixed tile is obtained by selecting
one of three translates of the frequency set. For odd modulus, the
remaining cardinalities are at least five. Strong induction separates
the prime-coordinate extension theorem from orders with no prime
factor of exponent one.
-/

open Finset AddChar ZMod
open scoped BigOperators ComplexConjugate

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1_H1_R1

section FiniteFourier

variable {L : ℕ} {χ : AddChar (ZMod L) ℂ}

private lemma tile_bijective {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, (p.1.1 : ZMod L) + p.2.1 = z) :
    Function.Bijective (fun p : A × B => (p.1.1 : ZMod L) + p.2.1) := by
  constructor
  · intro p q hpq
    obtain ⟨r, _, hr⟩ := h (q.1.1 + q.2.1)
    exact (hr p hpq).trans (hr q rfl).symm
  · intro z
    obtain ⟨p, hp, _⟩ := h z
    exact ⟨p, hp⟩

private lemma char_ne_zero (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (z : ZMod L) : χ z ≠ 0 := by
  rw [← ZMod.intCast_zmod_cast z, hχ]
  exact Complex.exp_ne_zero _

private lemma phase_conj {L : ℕ} (j : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((-j : ℤ) : ℂ) / (L : ℂ)) =
    conj (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (L : ℂ))) := by
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [Int.cast_neg, map_div₀, map_mul, map_ofNat, map_intCast, map_natCast,
    Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma char_conj (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (z : ZMod L) :
    χ (-z) = conj (χ z) := by
  rw [← ZMod.intCast_zmod_cast z, ← Int.cast_neg, hχ, hχ]
  exact phase_conj _

private lemma one_point {ℬ : Finset (Finset (ZMod L))}
    (h : ∀ B ∈ ℬ, B.card = 1) :
    ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  refine ⟨{0}, by simp, fun B hB => by simp [h B hB], ?_⟩
  intro B hB g hg j hj hgj
  simp only [mem_singleton] at hg hj
  exact (hgj (hg.trans hj.symm)).elim

private lemma neg_coeff (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {B : Finset (ZMod L)} {k : ZMod L}
    (h : (∑ b ∈ B, χ (k*b)) = 0) :
    (∑ b ∈ B, χ ((-k)*b)) = 0 := by
  simpa only [map_sum, map_zero, neg_mul, char_conj hχ] using congrArg conj h

private lemma double_coeff (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {B : Finset (ZMod L)} (hB : B.card = 3) {k : ZMod L}
    (h : (∑ b ∈ B, χ (k*b)) = 0) :
    (∑ b ∈ B, χ ((k+k)*b)) = 0 := by
  obtain ⟨u,v,w,huv,huw,hvw,rfl⟩ := Finset.card_eq_three.mp hB
  let f (b : ZMod L) := χ (k*b)
  have hu : u ∉ ({v,w} : Finset (ZMod L)) := by simp [huv,huw]
  have hv : v ∉ ({w} : Finset (ZMod L)) := by simp [hvw]
  have hs : f u + (f v + f w) = 0 := by
    change (∑ b ∈ ({u,v,w} : Finset (ZMod L)), f b) = 0 at h
    rwa [Finset.sum_insert hu, Finset.sum_insert hv, Finset.sum_singleton] at h
  have hc : conj (f u) + (conj (f v) + conj (f w)) = 0 := by
    simpa only [map_add, map_zero] using congrArg conj hs
  have hunit (b) : f b * conj (f b) = 1 := by
    dsimp [f]
    rw [← char_conj hχ, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hp : f u * f v + f u * f w + f v * f w = 0 := by
    calc
      _ = f u * f v * f w * (conj (f u) + (conj (f v) + conj (f w))) := by
        linear_combination -(f v*f w)*hunit u - (f u*f w)*hunit v - (f u*f v)*hunit w
      _ = 0 := by rw [hc,mul_zero]
  rw [Finset.sum_insert hu, Finset.sum_insert hv, Finset.sum_singleton]
  simp only [add_mul, AddChar.map_add_eq_mul]
  change f u*f u + (f v*f v + f w*f w) = 0
  linear_combination (f u + (f v + f w))*hs - 2*hp

variable [NeZero L]

private lemma tile_card {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    A.card * B.card = L := by
  simpa using Fintype.card_congr (Equiv.ofBijective _ (tile_bijective h))

private lemma char_eq_one (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {z : ZMod L} (h : χ z = 1) :
    z = 0 := by
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [← ZMod.intCast_zmod_cast z, hχ] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have he : ((z.val : ℤ) : ℂ) = (L : ℂ) * (k : ℂ) := by
    apply mul_left_cancel₀ hC
    have hm := (div_eq_iff hL).mp hk
    rw [ZMod.cast_eq_val] at hm
    linear_combination hm
  have he' : (z.val : ℤ) = (L : ℤ) * k := by exact_mod_cast he
  simpa using congrArg (fun t : ℤ => (t : ZMod L)) he'

private lemma char_sum (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) (k : ZMod L) :
    (∑ z : ZMod L, χ (k*z)) = if k = 0 then (L : ℂ) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    let f (z : ZMod L) := χ (k*z)
    have h : (∑ z : ZMod L, f (z+1)) = ∑ z, f z :=
      Fintype.sum_equiv (Equiv.addRight _) _ _ (fun _ => rfl)
    have hp : (∑ z, f z) * χ k = ∑ z, f z := by
      simpa only [f, mul_add, mul_one, AddChar.map_add_eq_mul, Finset.sum_mul] using h
    have hz : (∑ z, f z) * (χ k-1) = 0 := by
      rw [mul_sub, mul_one, hp, sub_self]
    exact (mul_eq_zero.mp hz).resolve_right
      (sub_ne_zero.mpr (fun he => hk (char_eq_one hχ he)))

private lemma tile_fourier (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A B : Finset (ZMod L)}
    (h : ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) {k : ZMod L} (hk : k ≠ 0) :
    (∑ a ∈ A, χ (k*a)) * (∑ b ∈ B, χ (k*b)) = 0 := by
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, χ (k*(a+b)) := by
      rw [Finset.sum_mul_sum]
      simp only [mul_add, AddChar.map_add_eq_mul]
    _ = ∑ z : ZMod L, χ (k*z) := by
      rw [← Finset.sum_coe_sort A]
      simp_rw [← Finset.sum_coe_sort B]
      let f (p : A × B) := χ (k*(p.1.1+p.2.1))
      calc
        _ = ∑ p : A × B, f p := (Fintype.sum_prod_type f).symm
        _ = _ := Fintype.sum_equiv (Equiv.ofBijective _ (tile_bijective h)) _ _ (fun _ => rfl)
    _ = 0 := by rw [char_sum hχ, if_neg hk]

private lemma coeff_ne_zero (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} (hA : 0 < A.card) (hproper : A.card < L) :
    ∃ k : ZMod L, k ≠ 0 ∧ (∑ a ∈ A, χ (k*a)) ≠ 0 := by
  classical
  by_contra! h
  have hproper' : A ≠ univ := by
    intro he
    simp [he] at hproper
  obtain ⟨x, hx⟩ : ∃ x, x ∉ A := by
    by_contra! hAll
    exact hproper' (Finset.eq_univ_of_forall hAll)
  have hz (k : ZMod L) :
      (∑ a ∈ A, χ (k*(a-x))) = if k = 0 then (A.card : ℂ) else 0 := by
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      simp only [sub_eq_add_neg, mul_add, AddChar.map_add_eq_mul, ← Finset.sum_mul, h k hk, zero_mul]
  have hEq : (A.card : ℂ) = 0 := by
    calc
      _ = ∑ k : ZMod L, ∑ a ∈ A, χ (k*(a-x)) := by simp [hz]
      _ = ∑ a ∈ A, ∑ k : ZMod L, χ ((a-x)*k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => by rw [mul_comm k]))
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hax : a ≠ x := fun he => hx (he ▸ ha)
        rw [char_sum hχ, if_neg (sub_ne_zero.mpr hax)]
  exact (Nat.cast_ne_zero.mpr hA.ne') hEq

private lemma all_freqs (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {ℬ : Finset (Finset (ZMod L))}
    (h : ∀ B ∈ ℬ, B.card = L) :
    ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  refine ⟨univ, by simp, fun B hB => by simp [h B hB], ?_⟩
  intro B hB g hg j hj hgj
  rw [B.eq_univ_of_card (by simpa using h B hB)]
  exact (char_sum hχ (g-j)).trans (if_neg (sub_ne_zero.mpr hgj))

private lemma three_point_complements (hχ : ∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) {A : Finset (ZMod L)} {ℬ : Finset (Finset (ZMod L))}
    (hA : 0 < A.card) (hproper : A.card < L) {B₀ : Finset (ZMod L)} (hB₀ : B₀ ∈ ℬ)
    (hcard : ∀ B ∈ ℬ, B.card = 3)
    (htile : ∀ B ∈ ℬ, ∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) :
    ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  obtain ⟨k,hk,hA'⟩ := coeff_ne_zero hχ hA hproper
  have hpos (B) (hB : B ∈ ℬ) : (∑ b ∈ B, χ (k*b)) = 0 :=
    (mul_eq_zero.mp (tile_fourier hχ (htile B hB) hk)).resolve_left hA'
  have hdbl (B) (hB : B ∈ ℬ) : (∑ b ∈ B, χ ((k+k)*b)) = 0 :=
    double_coeff hχ (hcard B hB) (hpos B hB)
  have hk2 : k+k ≠ 0 := by
    intro he
    have h := hdbl B₀ hB₀
    simp [he,hcard B₀ hB₀] at h
  have hkd : k+k ≠ k := by
    intro he
    exact hk (add_left_cancel (show k+k = k+0 by simpa using he))
  refine ⟨{0,k,k+k}, by simp, fun B hB =>
    (Finset.card_eq_three.mpr ⟨0,k,k+k,hk.symm,hk2.symm,hkd.symm,rfl⟩).trans (hcard B hB).symm, ?_⟩
  intro B hB g hg j hj hgj
  simp only [mem_insert, mem_singleton] at hg hj
  rcases hg with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl
  · exact (hgj rfl).elim
  · simpa only [zero_sub] using neg_coeff hχ (hpos B hB)
  · simpa only [zero_sub] using neg_coeff hχ (hdbl B hB)
  · simpa only [sub_zero] using hpos B hB
  · exact (hgj rfl).elim
  · simpa only [sub_add_cancel_left] using neg_coeff hχ (hpos B hB)
  · simpa only [sub_zero] using hdbl B hB
  · simpa only [add_sub_cancel_right] using hpos B hB
  · exact (hgj rfl).elim


private lemma char_injective (hχ : ∀ z : ℤ, χ (z : ZMod L) =
    Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) : Function.Injective χ := by
  intro x y h
  apply sub_eq_zero.mp
  apply char_eq_one hχ
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

private lemma three_point_tile (hχ : ∀ z : ℤ, χ (z : ZMod L) =
    Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ)))
    {A : Finset (ZMod L)} {ℬ : Finset (Finset (ZMod L))} (hA : A.card = 3)
    {B₀ : Finset (ZMod L)} (hB₀ : B₀ ∈ ℬ)
    (htile : ∀ B ∈ ℬ, ∀ z : ZMod L, ∃! p : A × B, p.1.1+p.2.1=z) :
    ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
      (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∑ b ∈ B, χ ((g-j)*b) = 0) := by
  classical
  obtain ⟨u,v,w,huv,huw,hvw,hpair⟩ := Finset.card_eq_three.mp hA
  have hsize (B) (hB : B ∈ ℬ) : 3 * B.card = L := by
    simpa only [hA] using tile_card (htile B hB)
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hBpos : 0 < B₀.card := by have := hsize B₀ hB₀; omega
  obtain ⟨η,hη,hηB⟩ := coeff_ne_zero hχ hBpos (by have := hsize B₀ hB₀; omega)
  have hηA : (∑ a ∈ A, χ (η*a)) = 0 :=
    (mul_eq_zero.mp (tile_fourier hχ (htile B₀ hB₀) hη)).resolve_right hηB
  let φ (g : ZMod L) := g*(v-u)
  have hφadd (g j : ZMod L) : φ (g+j) = φ g + φ j := add_mul _ _ _
  have hφsub (g j : ZMod L) : φ (g-j) = φ g - φ j := sub_mul _ _ _
  have hunit (z : ZMod L) : χ z * conj (χ z) = 1 := by
    rw [← char_conj hχ, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have root (k : ZMod L) (hk : (∑ a ∈ A, χ (k*a)) = 0) :
      χ (φ k) * χ (φ k) + χ (φ k) + 1 = 0 := by
    let x := χ (φ k)
    let y := χ (k*(w-u))
    have he : (∑ a ∈ A, χ (k*a)) = χ (k*u) * (1+(x+y)) := by
      rw [hpair, Finset.sum_insert (by simp [huv,huw]), Finset.sum_insert (by simp [hvw]),
        Finset.sum_singleton]
      have hv : k*v = k*u + φ k := by dsimp [φ]; ring
      have hw : k*w = k*u + k*(w-u) := by ring
      rw [hv,hw,AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
      dsimp [x,y]
      ring
    rw [he] at hk
    have hs : 1+(x+y) = 0 := (mul_eq_zero.mp hk).resolve_left (char_ne_zero hχ _)
    have hc : 1+(conj x+conj y) = 0 := by
      simpa only [map_one,map_zero,map_add] using congrArg conj hs
    have hx : x * conj x = 1 := hunit _
    have hy : y * conj y = 1 := hunit _
    have hxy : x*y = 1 := by
      linear_combination (x*y)*hc - y*hx - x*hy - hs
    change x*x+x+1=0
    linear_combination x*hs - hxy
  let δ := φ η
  let ω := χ δ
  have hω : ω*ω+ω+1=0 := root η hηA
  have hδ : δ ≠ 0 := by
    intro h
    have hw : ω = 1 := by simp [ω,h]
    norm_num [hw] at hω
  have hδrel : δ+δ = -δ := by
    apply char_injective hχ
    have hpos : χ (δ+δ)*χ δ = 1 := by
      rw [AddChar.map_add_eq_mul]
      change ω*ω*ω=1
      linear_combination (ω-1)*hω
    have hneg : χ (-δ)*χ δ = 1 := by
      rw [← AddChar.map_add_eq_mul,neg_add_cancel,AddChar.map_zero_eq_one]
    exact mul_right_cancel₀ (char_ne_zero hχ δ) (hpos.trans hneg.symm)
  have zeros (k : ZMod L) (hk : (∑ a ∈ A, χ (k*a)) = 0) :
      φ k = δ ∨ φ k = -δ := by
    have hsum : ω + χ (-δ) + 1 = 0 := by
      rw [← hδrel,AddChar.map_add_eq_mul]
      change ω+ω*ω+1=0
      linear_combination hω
    have hmul : ω*χ (-δ)=1 := by
      change χ δ * χ (-δ) = 1
      rw [← AddChar.map_add_eq_mul,add_neg_cancel,AddChar.map_zero_eq_one]
    have hprod : (χ (φ k)-ω)*(χ (φ k)-χ (-δ))=0 := by
      linear_combination root k hk - χ (φ k)*hsum + hmul
    rcases mul_eq_zero.mp hprod with h|h
    · exact Or.inl (char_injective hχ (sub_eq_zero.mp h))
    · exact Or.inr (char_injective hχ (sub_eq_zero.mp h))
  let f (g : ZMod L) := (φ g).val
  let P (g : ZMod L) : Prop := f g < f (g+η) ∧ f g < f (g-η)
  let Γ := (univ : Finset (ZMod L)).filter P
  have rot (g : ZMod L) : f (g+η+η) = f (g-η) := by
    change (φ (g+η+η)).val = (φ (g-η)).val
    rw [hφadd,hφadd,hφsub,add_assoc,show φ η+φ η = -φ η from hδrel,sub_eq_add_neg]
  have rot' (g : ZMod L) : f (g-η-η) = f (g+η) := by
    change (φ (g-η-η)).val = (φ (g+η)).val
    rw [hφsub,hφsub,hφadd,sub_sub,show φ η+φ η = -φ η from hδrel,sub_neg_eq_add]
  have forward_ne (g : ZMod L) : f g ≠ f (g+η) := by
    intro h
    have he : φ g = φ (g+η) := ZMod.val_injective L h
    rw [hφadd] at he
    apply hδ
    exact add_left_cancel (show φ g+δ = φ g+0 by simpa only [add_zero] using he.symm)
  have backward_ne (g : ZMod L) : f (g-η) ≠ f g := by
    simpa only [sub_add_cancel] using forward_ne (g-η)
  have orbit (g : ZMod L) : (if P g then 1 else 0) +
      (if P (g+η) then 1 else 0) + (if P (g-η) then 1 else 0) = (1 : ℕ) := by
    have hp : P (g+η) ↔ f (g+η) < f (g-η) ∧ f (g+η) < f g := by
      change (f (g+η) < f (g+η+η) ∧ f (g+η) < f (g+η-η)) ↔ _
      rw [rot,add_sub_cancel_right]
    have hm : P (g-η) ↔ f (g-η) < f g ∧ f (g-η) < f (g+η) := by
      change (f (g-η) < f (g-η+η) ∧ f (g-η) < f (g-η-η)) ↔ _
      rw [sub_add_cancel,rot']
    have hfg := forward_ne g
    have hbg := backward_ne g
    have hfb : f (g+η) ≠ f (g-η) := by rw [← rot]; exact forward_ne (g+η)
    rw [if_congr hp rfl rfl,if_congr hm rfl rfl]
    dsimp only [P]
    split_ifs <;> omega
  have shift (t : ZMod L) : ((univ : Finset (ZMod L)).filter (fun g => P (g+t))).card =
      Γ.card := by
    apply Finset.card_bij (fun g _ => g+t)
    · intro g hg
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hg).2⟩
    · intro _ _ _ _ h
      exact add_right_cancel h
    · intro j hj
      refine ⟨j-t, mem_filter.mpr ⟨mem_univ _, ?_⟩, sub_add_cancel _ _⟩
      simpa only [sub_add_cancel] using (mem_filter.mp hj).2
  have hcount : 3 * Γ.card = L := by
    have hs : (∑ g : ZMod L,
        ((if P g then 1 else 0) + (if P (g+η) then 1 else 0) +
          (if P (g-η) then 1 else 0) : ℕ)) = L := by simp [orbit]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter P univ,
      ← Finset.card_filter (fun g : ZMod L => P (g+η)) univ,
      ← Finset.card_filter (fun g : ZMod L => P (g-η)) univ] at hs
    have hs' : Γ.card + Γ.card + Γ.card = L := by
      simpa only [Γ, sub_eq_add_neg, shift] using hs
    omega
  have h0 : 0 ∈ Γ := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have hz : f 0 = 0 := by simp [f,φ]
    have hf := forward_ne 0
    have hb := backward_ne 0
    change f 0 < f (0+η) ∧ f 0 < f (0-η)
    omega
  have avoids (g j : ZMod L) (hg : P g) (hj : P j) : φ (g-j) ≠ δ := by
    intro he
    have hd : φ g-φ j = δ := (hφsub _ _).symm.trans he
    have eq : φ g = φ j+δ := by rw [← hd]; abel
    have hfe : f g = f (j+η) := by
      change (φ g).val = (φ (j+η)).val
      rw [eq,hφadd]
    have hbe : f (g-η) = f j := by
      change (φ (g-η)).val = (φ j).val
      rw [hφsub,eq,add_sub_cancel_right]
    have h1 := hg.2
    have h2 := hj.1
    omega
  refine ⟨Γ,h0,fun B hB => by have := hsize B hB; omega,?_⟩
  intro B hB g hg j hj hgj
  have hg' := (mem_filter.mp hg).2
  have hj' := (mem_filter.mp hj).2
  apply (mul_eq_zero.mp (tile_fourier hχ (htile B hB) (sub_ne_zero.mpr hgj))).resolve_left
  intro he
  rcases zeros (g-j) he with hp|hn
  · exact avoids g j hg' hj' hp
  · apply avoids j g hj' hg'
    have hneg : φ (j-g) = -φ (g-j) := by rw [hφsub,hφsub,neg_sub]
    rw [hneg,hn,neg_neg]

end FiniteFourier

private lemma odd_factors {a b : ℕ} (h : (a*b)%2=1) : a%2=1 ∧ b%2=1 := by
  rw [Nat.mul_mod] at h
  have ha : a%2 ≠ 0 := by intro hz; simp [hz] at h
  have hb : b%2 ≠ 0 := by intro hz; simp [hz] at h
  exact ⟨by omega,by omega⟩

/-- Prime-coordinate extension in odd order, the cyclic case of Zhou's theorem. -/
def H1 : Prop :=
  ∀ (M p : ℕ) [NeZero M] [NeZero (M*p)],
    M%2=1 → p%2=1 → p.Prime → ¬p ∣ M →
    (∀ (ψ : AddChar (ZMod M) ℂ), (∀ z : ℤ, ψ (z : ZMod M) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (M : ℂ))) →
      ∀ (A : Finset (ZMod M)) (ℬ : Finset (Finset (ZMod M))),
        (∀ B ∈ ℬ, ∀ z : ZMod M, ∃! q : A × B, q.1.1+q.2.1=z) →
        ∃ Γ : Finset (ZMod M), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
          (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j → ∑ b ∈ B, ψ ((g-j)*b)=0)) →
    ∀ (χ : AddChar (ZMod (M*p)) ℂ), (∀ z : ℤ, χ (z : ZMod (M*p)) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / ((M*p : ℕ) : ℂ))) →
    ∀ (A : Finset (ZMod (M*p))) (ℬ : Finset (Finset (ZMod (M*p)))),
      (∀ B ∈ ℬ, ∀ z : ZMod (M*p), ∃! q : A × B, q.1.1+q.2.1=z) →
      ∃ Γ : Finset (ZMod (M*p)), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
        (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j → ∑ b ∈ B, χ ((g-j)*b)=0)

/-- Odd orders with all prime factors repeated, for tilings with both factors of size at least five. -/
def H2 : Prop :=
  ∀ (L : ℕ) [NeZero L], L%2=1 → (∀ p : ℕ, p.Prime → p ∣ L → p*p ∣ L) →
    ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
    ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))), 5 ≤ A.card →
      (∀ B ∈ ℬ, 5 ≤ B.card ∧ ∀ z : ZMod L, ∃! q : A × B, q.1.1+q.2.1=z) →
      ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
        (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j → ∑ b ∈ B, χ ((g-j)*b)=0)

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1.H1 := by
  intro hExtend hRepeated
  have all : ∀ (L : ℕ) [NeZero L], L%2=1 →
      ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
        Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
      ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))),
        (∀ B ∈ ℬ, ∀ z : ZMod L, ∃! q : A × B, q.1.1+q.2.1=z) →
        ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ (∀ B ∈ ℬ, Γ.card = B.card) ∧
          (∀ B ∈ ℬ, ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j → ∑ b ∈ B, χ ((g-j)*b)=0) := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro inst hOdd χ hχ A ℬ htile
      classical
      by_cases hemp : ℬ = ∅
      · subst ℬ
        exact ⟨{0}, by simp⟩
      obtain ⟨B₀,hB₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hC := tile_card (htile B₀ hB₀)
      have hCards := odd_factors (hC ▸ hOdd)
      have hApos : 0 < A.card := by omega
      have hc (B) (hB : B ∈ ℬ) : B.card = B₀.card :=
        Nat.eq_of_mul_eq_mul_left hApos ((tile_card (htile B hB)).trans hC.symm)
      by_cases ha₁ : A.card = 1
      · exact all_freqs hχ (fun B hB => by rw [hc B hB]; simpa [ha₁] using hC)
      by_cases hb₁ : B₀.card = 1
      · exact one_point (fun B hB => (hc B hB).trans hb₁)
      by_cases ha₃ : A.card = 3
      · exact three_point_tile hχ ha₃ hB₀ htile
      by_cases hb₃ : B₀.card = 3
      · have hproper : A.card < L := by rw [hb₃,Nat.mul_comm] at hC; omega
        exact three_point_complements hχ hApos hproper hB₀ (fun B hB => (hc B hB).trans hb₃) htile
      by_cases hRep : ∀ p : ℕ, p.Prime → p ∣ L → p*p ∣ L
      · exact hRepeated L hOdd hRep χ hχ A ℬ (by omega)
          (fun B hB => ⟨by rw [hc B hB]; omega,htile B hB⟩)
      · have hEx : ∃ p : ℕ, p.Prime ∧ p ∣ L ∧ ¬p*p ∣ L := by
          by_contra! h
          exact hRep h
        obtain ⟨p,hp,hpL,hn⟩ := hEx
        obtain ⟨M,hM⟩ := hpL
        have hnp : ¬p ∣ M := by
          intro hh
          exact hn (hM ▸ mul_dvd_mul_left p hh)
        have hEq : L=M*p := hM.trans (Nat.mul_comm _ _)
        clear hM
        have ho := odd_factors (hEq ▸ hOdd)
        have hMpos : 0 < M := by omega
        have hLt : M < L := by
          rw [hEq]
          simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hMpos
        have : NeZero M := ⟨hMpos.ne'⟩
        subst L
        exact hExtend M p ho.1 ho.2 hp hnp (ih M hLt ho.1) χ hχ A ℬ htile
  intro L inst hOdd χ hχ A ℬ _ htile
  exact all L hOdd χ hχ A ℬ (fun B hB => (htile B hB).2)

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1_H1_R1
