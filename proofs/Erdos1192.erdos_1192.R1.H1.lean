import OMAReductions.R_Erdos1192_erdos_1192_R1
import Mathlib.NumberTheory.Bertrand

/-!
Ruzsa's square-mean bound for the representation function of an additive basis of order two.
We use signed parabolas in the plane over a prime field, together with the parabolas obtained
by swapping coordinates. The signed curves cover every vector by sums. A fixed number of
translates corrects the carries in the integer encoding and covers a full interval at each
geometric scale. The unique nonzero differences on each curve bound the energy of all pairs
of blocks, including blocks at different scales.
-/

open Finset Filter Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace QuadraticBasis

private def curve {p : ℕ} (swap neg : Bool) (x : ZMod p) : ZMod p × ZMod p :=
  let u := if neg then -x else x
  let v := if neg then -(x^2) else x^2
  if swap then (v,u) else (u,v)

private def packed {p : ℕ} (xy : ZMod p × ZMod p) : ℕ :=
  xy.1.val + (2*p) * xy.2.val

private lemma packed_lt {p : ℕ} [NeZero p] (xy : ZMod p × ZMod p) :
    packed xy < 2*p^2 := by
  have h₁ := ZMod.val_lt xy.1
  have h₂ := ZMod.val_lt xy.2
  have hp := NeZero.pos p
  unfold packed
  have h := Nat.mul_le_mul_left (2*p) (show xy.2.val + 1 ≤ p by omega)
  rw [Nat.mul_add, Nat.mul_one] at h
  nlinarith

private lemma packed_sum_eq {p : ℕ} [NeZero p] {u v w z : ZMod p × ZMod p}
    (h : packed u + packed v = packed w + packed z) : u + v = w + z := by
  have hu := ZMod.val_lt u.1
  have hv := ZMod.val_lt v.1
  have hw := ZMod.val_lt w.1
  have hz := ZMod.val_lt z.1
  have h₁ : u.1.val + v.1.val = w.1.val + z.1.val := by
    have hh := congrArg (fun n => n % (2*p)) h
    simp only [packed] at hh
    rw [show (u.1.val + 2*p*u.2.val + (v.1.val + 2*p*v.2.val)) =
        (u.1.val + v.1.val) + (2*p)*(u.2.val+v.2.val) by ring,
      show (w.1.val + 2*p*w.2.val + (z.1.val + 2*p*z.2.val)) =
        (w.1.val + z.1.val) + (2*p)*(w.2.val+z.2.val) by ring,
      Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hh
    exact hh
  have h₂ : u.2.val + v.2.val = w.2.val + z.2.val := by
    have h' : (u.1.val + v.1.val) + (2*p)*(u.2.val+v.2.val) =
        (w.1.val + z.1.val) + (2*p)*(w.2.val+z.2.val) := by
      unfold packed at h
      linear_combination h
    rw [h₁] at h'
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by decide : 0 < 2) (NeZero.pos p)) (Nat.add_left_cancel h')
  apply Prod.ext
  · have H := congrArg (fun n : ℕ => (n : ZMod p)) h₁
    simpa using H
  · have H := congrArg (fun n : ℕ => (n : ZMod p)) h₂
    simpa using H

private lemma two_ne {p : ℕ} [Fact p.Prime] (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact h)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) h')

private lemma curve_diff_inj {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (swap neg : Bool) {a b c d : ZMod p} (hab : a ≠ b)
    (h : curve swap neg a + curve swap neg d = curve swap neg c + curve swap neg b) :
    a = c ∧ b = d := by
  have h₁ : a - b = c - d := by
    cases swap <;> cases neg
    · have H := congrArg Prod.fst h
      simp only [curve, Bool.false_eq_true, if_false, Prod.fst_add] at H
      linear_combination H
    · have H := congrArg Prod.fst h
      simp only [curve, Bool.false_eq_true, if_false, if_true, Prod.fst_add] at H
      linear_combination -H
    · have H := congrArg Prod.snd h
      simp only [curve, Bool.false_eq_true, if_false, if_true, Prod.snd_add] at H
      linear_combination H
    · have H := congrArg Prod.snd h
      simp only [curve, if_true, Prod.snd_add] at H
      linear_combination -H
  have h₂ : a^2 - b^2 = c^2 - d^2 := by
    cases swap <;> cases neg
    · have H := congrArg Prod.snd h
      simp only [curve, Bool.false_eq_true, if_false, Prod.snd_add] at H
      linear_combination H
    · have H := congrArg Prod.snd h
      simp only [curve, Bool.false_eq_true, if_false, if_true, Prod.snd_add] at H
      linear_combination -H
    · have H := congrArg Prod.fst h
      simp only [curve, Bool.false_eq_true, if_false, if_true, Prod.fst_add] at H
      linear_combination H
    · have H := congrArg Prod.fst h
      simp only [curve, if_true, Prod.fst_add] at H
      linear_combination -H
  have h₃ : (a-b)*(a+b) = (a-b)*(c+d) := by
    rw [show (a-b)*(a+b) = a^2-b^2 by ring, h₂, h₁]
    ring
  have h₄ := mul_left_cancel₀ (sub_ne_zero.mpr hab) h₃
  constructor
  · exact mul_left_cancel₀ (two_ne hp) (by linear_combination h₁ + h₄)
  · exact mul_left_cancel₀ (two_ne hp) (by linear_combination h₄ - h₁)

private lemma parabola_cover {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (s t : ZMod p) (hs : s ≠ 0) :
    ∃ a b : ZMod p, a - b = s ∧ a^2 - b^2 = t := by
  let a := (t+s^2)/(2*s)
  refine ⟨a, a-s, by ring, ?_⟩
  have ha : a*(2*s) = t+s^2 := by
    apply div_mul_cancel₀
    exact mul_ne_zero (two_ne hp) hs
  linear_combination ha

private lemma curve_cover {p : ℕ} [Fact p.Prime] (hp : 2 < p) (u : ZMod p × ZMod p) :
    ∃ swap : Bool, ∃ a b : ZMod p, curve swap false a + curve swap true b = u := by
  rcases u with ⟨s,t⟩
  by_cases hs : s = 0
  · by_cases ht : t = 0
    · subst s t
      exact ⟨false, 0, 0, by simp [curve]⟩
    · obtain ⟨a,b,h₁,h₂⟩ := parabola_cover hp t s ht
      exact ⟨true, a, b, Prod.ext (by simpa [curve, sub_eq_add_neg] using h₂)
        (by simpa [curve, sub_eq_add_neg] using h₁)⟩
  · obtain ⟨a,b,h₁,h₂⟩ := parabola_cover hp s t hs
    exact ⟨false, a, b, Prod.ext (by simpa [curve, sub_eq_add_neg] using h₁)
      (by simpa [curve, sub_eq_add_neg] using h₂)⟩


private def uniqueDiff (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → a+d = c+b → a = c ∧ b = d

private def hits (S T : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ T).filter fun v => v.1 + v.2 = n

private lemma hits_mem {S T : Finset ℕ} {n : ℕ} {v : ℕ × ℕ} :
    v ∈ hits S T n ↔ v.1 ∈ S ∧ v.2 ∈ T ∧ v.1+v.2 = n := by
  simp [hits, and_assoc]

private lemma pair_energy (S T : Finset ℕ) (hS : uniqueDiff S) (hT : uniqueDiff T) (x : ℕ) :
    (∑ n ∈ range (x+1), (hits S T n).card ^ 2) ≤ 2*S.card*T.card := by
  let F (n : ℕ) := hits S T n ×ˢ hits S T n
  have hdis : (↑(range (x+1)) : Set ℕ).PairwiseDisjoint F := by
    intro n hn m hm hnm
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have h₁ := (hits_mem.mp (mem_product.mp hy).1).2.2
    have h₂ := (hits_mem.mp (mem_product.mp hy').1).2.2
    exact hnm (h₁.symm.trans h₂)
  let C := (range (x+1)).biUnion F
  have hCard : C.card = ∑ n ∈ range (x+1), (hits S T n).card ^ 2 := by
    rw [show C = (range (x+1)).biUnion F from rfl, card_biUnion hdis]
    simp [F, pow_two]
  have hC (z : (ℕ × ℕ) × (ℕ × ℕ)) (hz : z ∈ C) :
      z.1.1 ∈ S ∧ z.2.1 ∈ S ∧ z.1.2 ∈ T ∧ z.2.2 ∈ T ∧
        z.1.1 + z.1.2 = z.2.1 + z.2.2 := by
    obtain ⟨n, hn, h⟩ := mem_biUnion.mp hz
    obtain ⟨h₁,h₂⟩ := mem_product.mp h
    exact ⟨(hits_mem.mp h₁).1, (hits_mem.mp h₂).1, (hits_mem.mp h₁).2.1,
      (hits_mem.mp h₂).2.1, (hits_mem.mp h₁).2.2.trans (hits_mem.mp h₂).2.2.symm⟩
  let D := C.filter fun z => z.1.1 = z.2.1
  let E := C.filter fun z => z.1.1 ≠ z.2.1
  have hDiag : D.card ≤ S.card*T.card := by
    rw [← card_product]
    apply card_le_card_of_injOn Prod.fst
    · intro z hz
      obtain ⟨h1, _, h2, _, _⟩ := hC z (mem_filter.mp hz).1
      exact mem_product.mpr ⟨h1,h2⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hz ⟨⟨a',b'⟩,⟨c',d'⟩⟩ hz' he
      simp only [Prod.mk.injEq] at he ⊢
      have h₁ := (mem_filter.mp hz).2
      have h₂ := (mem_filter.mp hz').2
      have h₃ := (hC _ (mem_filter.mp hz).1).2.2.2.2
      have h₄ := (hC _ (mem_filter.mp hz').1).2.2.2.2
      change a = c at h₁
      change a' = c' at h₂
      change a+b = c+d at h₃
      change a'+b' = c'+d' at h₄
      exact ⟨he, by omega, by omega⟩
  have hOffS : E.card ≤ S.card*S.card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun z => (z.1.1,z.2.1))
    · intro z hz
      have h := hC z (mem_filter.mp hz).1
      exact mem_product.mpr ⟨h.1,h.2.1⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hz ⟨⟨a',b'⟩,⟨c',d'⟩⟩ hz' he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨_,_,hb,hd,he⟩ := hC _ (mem_filter.mp hz).1
      obtain ⟨_,_,hb',hd',he'⟩ := hC _ (mem_filter.mp hz').1
      have hac : a ≠ c := (mem_filter.mp hz).2
      change a+b = c+d at he
      change a+b' = c+d' at he'
      have hbd := hT b hb d hd b' hb' d' hd' (by omega) (by omega)
      simp [hbd.1, hbd.2]
  have hOffT : E.card ≤ T.card*T.card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun z => (z.1.2,z.2.2))
    · intro z hz
      have h := hC z (mem_filter.mp hz).1
      exact mem_product.mpr ⟨h.2.2.1,h.2.2.2.1⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hz ⟨⟨a',b'⟩,⟨c',d'⟩⟩ hz' he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨ha,hc,_,_,he⟩ := hC _ (mem_filter.mp hz).1
      obtain ⟨ha',hc',_,_,he'⟩ := hC _ (mem_filter.mp hz').1
      have hac : a ≠ c := (mem_filter.mp hz).2
      change a+b = c+d at he
      change a'+b = c'+d at he'
      have hca := hS a ha c hc a' ha' c' hc' hac (by omega)
      simp [hca.1, hca.2]
  have hoff : E.card ≤ S.card*T.card := by
    rcases Nat.le_total S.card T.card with h | h
    · exact hOffS.trans (Nat.mul_le_mul_left _ h)
    · exact hOffT.trans (Nat.mul_le_mul_right _ h)
  rw [← hCard, ← card_filter_add_card_filter_not (s := C) (p := fun z => z.1.1 = z.2.1)]
  change D.card + E.card ≤ _
  nlinarith

private abbrev Kind := Bool × Bool × Fin 3 × Fin 101

private def offset (p M : ℕ) (g : Kind) : ℕ :=
  M + p*g.2.2.1.val + 2*p^2*g.2.2.2.val

private def chunk (p M : ℕ) [NeZero p] (g : Kind) : Finset ℕ :=
  univ.image fun x : ZMod p => offset p M g + packed (curve g.1 g.2.1 x)

private lemma chunk_card (p M : ℕ) [NeZero p] (g : Kind) : (chunk p M g).card ≤ p := by
  unfold chunk
  exact card_image_le.trans_eq (by simp [ZMod.card])

private lemma chunk_min {p M : ℕ} [NeZero p] {g : Kind} {n : ℕ} (hn : n ∈ chunk p M g) :
    M ≤ n := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
  unfold offset
  omega

private lemma chunk_sidon (p M : ℕ) [Fact p.Prime] (hp : 2 < p) (g : Kind) :
    uniqueDiff (chunk p M g) := by
  intro a ha b hb c hc d hd hab hsum
  obtain ⟨a, -, rfl⟩ := mem_image.mp ha
  obtain ⟨b, -, rfl⟩ := mem_image.mp hb
  obtain ⟨c, -, rfl⟩ := mem_image.mp hc
  obtain ⟨d, -, rfl⟩ := mem_image.mp hd
  have he : packed (curve g.1 g.2.1 a) + packed (curve g.1 g.2.1 d) =
      packed (curve g.1 g.2.1 c) + packed (curve g.1 g.2.1 b) := by omega
  obtain ⟨rfl, rfl⟩ := curve_diff_inj hp g.1 g.2.1 (by rintro rfl; exact hab rfl)
    (packed_sum_eq he)
  exact ⟨rfl,rfl⟩

private lemma carry {p : ℕ} [NeZero p] {a b : ZMod p} {r : ℕ} (hr : r < p)
    (h : a+b = (r : ZMod p)) :
    ∃ c : ℕ, c ≤ 1 ∧ a.val + b.val = r + p*c := by
  have hmod : (a.val + b.val) % p = r := by
    rw [← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      h, ZMod.val_natCast_of_lt hr]
  have hlt : a.val + b.val < 2*p := by have h₁ := ZMod.val_lt a; have h₂ := ZMod.val_lt b; omega
  refine ⟨(a.val+b.val)/p, ?_, ?_⟩
  · have hc := (Nat.div_lt_iff_lt_mul (NeZero.pos p)).mpr hlt
    omega
  · rw [← hmod]
    exact (Nat.mod_add_div _ _).symm

private lemma chunk_cover (p M : ℕ) [Fact p.Prime] (hp : 2 < p) {n : ℕ}
    (hn₁ : 2*M + p + 2*p^2 ≤ n) (hn₂ : n < 2*M + p + 2*p^2+100*(2*p^2)) :
    ∃ g h : Kind, ∃ a ∈ chunk p M g, ∃ b ∈ chunk p M h, a+b=n := by
  let t := n - (2*M+p+2*p^2)
  let j := t / (2*p^2)
  let l := t % (2*p^2)
  let lo := l % (2*p)
  let hi := l / (2*p)
  let r := lo % p
  let u := lo / p
  have hq : 0 < 2*p^2 := by positivity
  have h2p : 0 < 2*p := by positivity
  have ht : t < 100*(2*p^2) := by dsimp [t]; omega
  have hj : j < 100 := (Nat.div_lt_iff_lt_mul hq).mpr ht
  have hl : l < 2*p^2 := Nat.mod_lt _ hq
  have hlo : lo < 2*p := Nat.mod_lt _ h2p
  have hhi : hi < p := (Nat.div_lt_iff_lt_mul h2p).mpr (by
    convert hl using 1
    ring)
  have hr : r < p := Nat.mod_lt _ (by omega)
  have hu : u < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlo
  obtain ⟨swap,a,b,hab⟩ := curve_cover hp ((r : ZMod p), (hi : ZMod p))
  let A := curve swap false a
  let B := curve swap true b
  have hc₁ : A.1+B.1 = (r : ZMod p) := congrArg Prod.fst hab
  have hc₂ : A.2+B.2 = (hi : ZMod p) := congrArg Prod.snd hab
  obtain ⟨c₁, hc₁le, hc₁val⟩ := carry hr hc₁
  obtain ⟨c₂, hc₂le, hc₂val⟩ := carry hhi hc₂
  let U : Fin 3 := ⟨u+1-c₁, by omega⟩
  let J : Fin 101 := ⟨j+1-c₂, by omega⟩
  let g : Kind := (swap,false,U,J)
  let h : Kind := (swap,true,0,0)
  refine ⟨g,h,offset p M g + packed A, mem_image.mpr ⟨a, mem_univ _,rfl⟩,
    offset p M h + packed B, mem_image.mpr ⟨b, mem_univ _,rfl⟩, ?_⟩
  have hU : U.val+c₁ = u+1 := by
    change u+1-c₁+c₁ = u+1
    exact Nat.sub_add_cancel (hc₁le.trans (Nat.le_add_left 1 u))
  have hJ : J.val+c₂ = j+1 := by
    change j+1-c₂+c₂ = j+1
    exact Nat.sub_add_cancel (hc₂le.trans (Nat.le_add_left 1 j))
  have hdecomp₁ : l + (2*p^2)*j = t := Nat.mod_add_div _ _
  have hdecomp₂ : lo+(2*p)*hi = l := Nat.mod_add_div _ _
  have hdecomp₃ : r+p*u = lo := Nat.mod_add_div _ _
  have hdecomp : t + (2*M+p+2*p^2) = n := by dsimp [t]; omega
  change M+p*U.val+2*p^2*J.val+(A.1.val+2*p*A.2.val) +
    (M+p*0+2*p^2*0+(B.1.val+2*p*B.2.val)) = n
  calc
    _ = 2*M + p*(U.val+c₁) + 2*p^2*(J.val+c₂) + (r+2*p*hi) := by
      have H : (p : ℤ)*(A.2.val+B.2.val) = (p : ℤ)*(hi+p*c₂) := by
        exact_mod_cast congrArg (p * ·) hc₂val
      zify at hc₁val ⊢
      linear_combination hc₁val + 2*H
    _ = n := by
      rw [hU, hJ]
      linear_combination hdecomp + hdecomp₁ + hdecomp₂ + hdecomp₃

private def primeAt (i : ℕ) : ℕ :=
  (Nat.bertrand (4^(i+1)) (by positivity)).choose

private lemma primeAt_spec (i : ℕ) :
    (primeAt i).Prime ∧ 4^(i+1) < primeAt i ∧ primeAt i ≤ 2*4^(i+1) :=
  (Nat.bertrand (4^(i+1)) (by positivity)).choose_spec

private local instance primeAt_fact (i : ℕ) : Fact (primeAt i).Prime :=
  ⟨(primeAt_spec i).1⟩

private def scale (i : ℕ) : ℕ := 16^(i+1)

private lemma scale_succ (i : ℕ) : scale (i+1) = 16*scale i := by
  unfold scale
  rw [pow_succ, mul_comm]

private def block (i : ℕ) (g : Kind) : Finset ℕ := chunk (primeAt i) (scale i) g

private def basis : Set ℕ := {n | ∃ i g, n ∈ block i g}

private lemma cover_scale (i : ℕ) {n : ℕ} (hn₁ : 12*scale i ≤ n)
    (hn₂ : n < 12*scale (i+1)) : ∃ a ∈ basis, ∃ b ∈ basis, a+b=n := by
  have hs : (4^(i+1) : ℕ)^2 = scale i := by rw [scale, ← pow_mul, mul_comm, pow_mul]; rfl
  have hp := primeAt_spec i
  have hc : 2 < primeAt i := by
    have H : (4 : ℕ) ≤ 4^(i+1) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 4) (show 1 ≤ i+1 by omega)
    omega
  have hp₁ : scale i ≤ (primeAt i)^2 := hs ▸ Nat.pow_le_pow_left hp.2.1.le 2
  have hp₂ : (primeAt i)^2 ≤ 4*scale i := by
    have H := Nat.pow_le_pow_left hp.2.2 2
    rwa [mul_pow, hs] at H
  have hp₃ : primeAt i ≤ scale i := by
    have H : (4 : ℕ) ≤ 4^(i+1) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 4) (show 1 ≤ i+1 by omega)
    nlinarith [hp.2.2]
  obtain ⟨g,h,a,ha,b,hb,hab⟩ := chunk_cover (primeAt i) (scale i) hc (n := n)
    (by omega) (by rw [scale_succ] at hn₂; omega)
  exact ⟨a, ⟨i,g,ha⟩, b, ⟨i,h,hb⟩,hab⟩

private lemma eventually_cover : ∀ᶠ n : ℕ in atTop, ∃ a ∈ basis, ∃ b ∈ basis, a+b=n := by
  filter_upwards [eventually_ge_atTop 192] with n hn
  let j := Nat.log 16 (n/12)
  have hn' : 16 ≤ n/12 := by omega
  have hj : 1 ≤ j := (Nat.le_log_iff_pow_le (by decide) (by omega : n/12 ≠ 0)).2 (by simpa using hn')
  have hs : scale (j-1) = 16^j := by rw [scale, Nat.sub_add_cancel hj]
  have ha : 16^j ≤ n/12 := Nat.pow_log_le_self _ (by omega)
  have hb : n/12 < 16^(j+1) := Nat.lt_pow_succ_log_self (by decide) (n/12)
  apply cover_scale (j-1) (by rw [hs]; omega)
  rw [show (j-1)+1 = j by omega, scale]
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 12)).mp (by simpa using hb) |>.trans_eq (mul_comm _ _)

private def reps (A : Set ℕ) (n : ℕ) : Set (Fin 2 → ℕ) :=
  {v | (∀ i, v i ∈ A) ∧ v 0 + v 1 = n}

private lemma f_two_eq (A : Set ℕ) (n : ℕ) : Erdos1192.f_r A 2 n = (reps A n).ncard := by
  unfold Erdos1192.f_r reps
  simp only [Fin.sum_univ_two]

private def firstTwo (v : Fin 2 → ℕ) : ℕ × ℕ := (v 0, v 1)

private lemma firstTwo_inj : Function.Injective firstTwo := by
  intro v w hvw
  funext i
  fin_cases i
  · exact congrArg Prod.fst hvw
  · exact congrArg Prod.snd hvw

private lemma reps_finite (A : Set ℕ) (n : ℕ) : (reps A n).Finite := by
  apply Set.Finite.of_injOn (f := firstTwo) (t := (Set.Iic n ×ˢ Set.Iic n)) _
    firstTwo_inj.injOn ((Set.finite_Iic n).prod (Set.finite_Iic n))
  intro v hv
  have he : v 0+v 1=n := hv.2
  exact ⟨by change v 0 ≤ n; omega, by change v 1 ≤ n; omega⟩

private lemma reps_pos {A : Set ℕ} {a b n : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hn : a+b=n) :
    0 < Erdos1192.f_r A 2 n := by
  rw [f_two_eq]
  apply (Set.ncard_pos (reps_finite A n)).2
  refine ⟨![a,b], ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · exact hn

private abbrev BlockIndex := ℕ × Kind

private def blockOf (k : BlockIndex) : Finset ℕ := block k.1 k.2

private def indices (x : ℕ) : Finset BlockIndex :=
  range (Nat.log 16 x + 1) ×ˢ (univ : Finset Kind)

private lemma index_mem {x a : ℕ} {k : BlockIndex}
    (hx : x ≠ 0) (ha : a ≤ x) (hb : a ∈ blockOf k) : k ∈ indices x := by
  have he : scale k.1 ≤ x := (chunk_min hb).trans ha
  change 16^(k.1+1) ≤ x at he
  have h := (Nat.le_log_iff_pow_le (by decide : 1 < 16) hx).2 he
  refine mem_product.mpr ⟨mem_range.mpr (by omega), mem_univ _⟩

private def combined (k : BlockIndex × BlockIndex) (n : ℕ) : ℝ :=
  (hits (blockOf k.1) (blockOf k.2) n).card

private lemma reps_bound {x n : ℕ} (hx : x ≠ 0) (hn : n ≤ x) :
    (Erdos1192.f_r basis 2 n : ℝ) ≤
      ∑ k ∈ indices x ×ˢ indices x, combined k n := by
  let I := indices x ×ˢ indices x
  let R : Finset (ℕ × ℕ) := I.biUnion fun k => hits (blockOf k.1) (blockOf k.2) n
  have hmap : Set.MapsTo firstTwo (reps basis n) (R : Set (ℕ × ℕ)) := by
    intro v hv
    obtain ⟨hin, hs⟩ := hv
    obtain ⟨i,g,hi⟩ := hin 0
    obtain ⟨j,h,hj⟩ := hin 1
    exact mem_biUnion.mpr ⟨((i,g),(j,h)),
      mem_product.mpr ⟨index_mem hx (by omega) hi, index_mem hx (by omega) hj⟩,
      hits_mem.mpr ⟨hi,hj,hs⟩⟩
  have h := Set.ncard_le_ncard_of_injOn firstTwo hmap firstTwo_inj.injOn R.finite_toSet
  rw [Set.ncard_coe_finset] at h
  rw [f_two_eq]
  unfold combined
  exact_mod_cast h.trans (card_biUnion_le (s := I) (t := fun k => hits (blockOf k.1) (blockOf k.2) n))

private def weight (k : BlockIndex) : ℝ := 2^(k.1+1)

private lemma weight_nonneg (k : BlockIndex) : 0 ≤ weight k := by unfold weight; positivity

private lemma block_card_real (k : BlockIndex) :
    ((blockOf k).card : ℝ) ≤ 2 * (weight k)^2 := by
  have h := (chunk_card (primeAt k.1) (scale k.1) k.2).trans (primeAt_spec k.1).2.2
  have h' : ((blockOf k).card : ℝ) ≤ 2*(4:ℝ)^(k.1+1) := by exact_mod_cast h
  have he : (weight k)^2 = (4:ℝ)^(k.1+1) := by unfold weight; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rwa [he]

private lemma block_sidon (k : BlockIndex) : uniqueDiff (blockOf k) := by
  apply chunk_sidon
  have h := (primeAt_spec k.1).2.1
  have hf : (4:ℕ) ≤ 4^(k.1+1) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 4) (show 1 ≤ k.1+1 by omega)
  omega

private lemma combined_energy (k : BlockIndex × BlockIndex) (x : ℕ) :
    (∑ n ∈ range (x+1), combined k n ^ 2) ≤
      8 * (weight k.1 * weight k.2)^2 := by
  have h := pair_energy (blockOf k.1) (blockOf k.2) (block_sidon _) (block_sidon _) x
  have h' : (∑ n ∈ range (x+1), combined k n ^ 2) ≤
      2 * ((blockOf k.1).card : ℝ)*((blockOf k.2).card : ℝ) := by
    unfold combined
    exact_mod_cast h
  refine h'.trans ?_
  calc
    _ ≤ (2 : ℝ) * (2*(weight k.1)^2) * (2*(weight k.2)^2) := by
      gcongr <;> apply block_card_real
    _ = _ := by ring

private lemma sum_block_energy (I : Finset (BlockIndex × BlockIndex)) (x : ℕ) :
    (∑ n ∈ range (x+1), (∑ k ∈ I, combined k n)^2) ≤
      8 * (∑ k ∈ I, weight k.1 * weight k.2)^2 := by
  let w (k : BlockIndex × BlockIndex) := weight k.1 * weight k.2
  have hw (k : BlockIndex × BlockIndex) : 0 ≤ w k := mul_nonneg (weight_nonneg _) (weight_nonneg _)
  have hp (k l : BlockIndex × BlockIndex) :
      (∑ n ∈ range (x+1), combined k n * combined l n) ≤ 8*w k*w l := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide)
      (mul_nonneg (mul_nonneg (by norm_num) (hw k)) (hw l))
    calc
      _ ≤ (∑ n ∈ range (x+1), combined k n ^ 2) *
          (∑ n ∈ range (x+1), combined l n ^ 2) :=
        sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (8*(w k)^2)*(8*(w l)^2) := by
        gcongr <;> apply combined_energy
      _ = _ := by ring
  calc
    _ = ∑ k ∈ I, ∑ l ∈ I, ∑ n ∈ range (x+1), combined k n * combined l n := by
      simp_rw [pow_two, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      exact sum_comm
    _ ≤ ∑ k ∈ I, ∑ l ∈ I, 8*w k*w l :=
      sum_le_sum fun k _ => sum_le_sum fun l _ => hp k l
    _ = _ := by
      calc
        _ = ∑ k ∈ I, (8*w k)*(∑ l ∈ I, w l) := by simp_rw [mul_sum]
        _ = (∑ k ∈ I, 8*w k)*(∑ l ∈ I, w l) := by rw [sum_mul]
        _ = _ := by rw [← mul_sum, pow_two]; ring

private lemma geometric (m : ℕ) : (∑ i ∈ range m, (2:ℝ)^(i+1)) ≤ 2^(m+1) := by
  induction m with
  | zero => norm_num
  | succ m hm =>
      rw [sum_range_succ, pow_succ' _ (m+1)]
      linarith

private lemma indices_weight (x : ℕ) :
    (∑ k ∈ indices x, weight k) ≤ 1212 * (2:ℝ)^(Nat.log 16 x + 2) := by
  unfold indices
  rw [sum_product]
  simp_rw [weight]
  have hk : Fintype.card Kind = 1212 := by norm_num [Kind, Fintype.card_prod]
  simp only [sum_const, card_univ, hk, nsmul_eq_mul, Nat.cast_ofNat, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (geometric _) (by positivity)

private lemma bound_sum {x : ℕ} (hx : x ≠ 0) :
    (∑ n ∈ range (x+1), (Erdos1192.f_r basis 2 n : ℝ)^2) ≤
      (8 * 1212^4 * 16^2 : ℝ) * x := by
  have hp : ((16:ℝ)^(Nat.log 16 x)) ≤ x := by exact_mod_cast Nat.pow_log_le_self 16 hx
  have hw := indices_weight x
  calc
    _ ≤ ∑ n ∈ range (x+1), (∑ k ∈ indices x ×ˢ indices x, combined k n)^2 := by
      apply sum_le_sum
      intro n hn
      gcongr
      exact reps_bound hx (by have h := mem_range.mp hn; omega)
    _ ≤ 8 * (∑ k ∈ indices x ×ˢ indices x, weight k.1 * weight k.2)^2 :=
      sum_block_energy _ x
    _ = 8 * (∑ k ∈ indices x, weight k)^4 := by rw [sum_product]; simp [← mul_sum, ← sum_mul]; ring
    _ ≤ 8 * (1212 * (2:ℝ)^(Nat.log 16 x+2))^4 := by
      gcongr
      exact sum_nonneg fun i _ => weight_nonneg i
    _ = (8 * 1212^4 * 16^2 : ℝ) * 16^(Nat.log 16 x) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, pow_add]
      ring
    _ ≤ _ := by gcongr

end QuadraticBasis

open QuadraticBasis

theorem OMA.root_solution : type_of% @Erdos1192.erdos_1192.variants.ruzsa := by
  refine ⟨basis, eventually_cover.mono ?_, ?_⟩
  · rintro n ⟨a,ha,b,hb,hab⟩
    exact reps_pos ha hb hab
  · refine Asymptotics.IsBigO.of_bound (8*1212^4*16^2) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    have hs : (0 : ℝ) ≤ ∑ n ∈ range (x + 1), (Erdos1192.f_r basis 2 n : ℝ)^2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
      using bound_sum (show x ≠ 0 by omega)

/-- The step statement is the root statement `Erdos1192.erdos_1192.variants.ruzsa`, whose merged proof is reused above. -/
theorem OMA.solution : OMA.R_Erdos1192_erdos_1192_R1.H1 := OMA.root_solution
