import OMAReductions.R_Selfridge_selfridge_seq_conjecture_R1
import Mathlib

-- Step Selfridge.selfridge_seq_conjecture.R1.H1: hypothesis H1 of reduction Selfridge.selfridge_seq_conjecture.R1
-- Credit: @ivillar

/-!
`F_12 = 2 ^ 4096 + 1` is the product of six pairwise coprime known factors and a cofactor `cof`
of 1133 digits that is coprime to all of them. Each known factor contributes at least one prime.
The cofactor contributes at least two: if `cof` were a prime power `p ^ k`, then `3 ^ cof = 3` in
`ZMod p`, so `p` would divide `gcd (3 ^ cof - 3) cof`; but a kernel computation (modular
exponentiation by repeated squaring) shows that this gcd is `1`. Hence `F_12` has at least eight
distinct prime factors.
-/

namespace F2SelfSeq

/-- Forces the kernel to evaluate `x` before calling `f` (the value is shared afterwards). -/
def force (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  match x with
  | 0 => f 0
  | n + 1 => f (n + 1)

theorem force_eq (x : ℕ) (f : ℕ → ℕ) : force x f = f x := by
  cases x <;> rfl

/-- `pm m fuel acc b e` is `acc * b ^ e` modulo `m`, by repeated squaring. -/
def pm (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _ => acc
  | fuel + 1, acc, b, e =>
    force e fun e => force acc fun acc => force b fun b =>
      if e = 0 then acc
      else pm m fuel (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2)

theorem pm_spec (m : ℕ) : ∀ fuel acc b e : ℕ, e < 2 ^ fuel →
    pm m fuel acc b e ≡ acc * b ^ e [MOD m] := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc b e he
    have h0 : e = 0 := by simpa using he
    subst h0
    rw [pm, pow_zero, mul_one]
  | succ fuel ih =>
    intro acc b e he
    rw [pm, force_eq, force_eq, force_eq]
    by_cases h0 : e = 0
    · subst h0
      rw [if_pos rfl, pow_zero, mul_one]
    · rw [if_neg h0]
      have he2 : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      have h := ih (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2) he2
      have h2 : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1] at h ⊢
        have h3 : acc * b ^ e = acc * b * (b * b) ^ (e / 2) := by
          have h4 : e = 2 * (e / 2) + 1 := by omega
          conv_lhs => rw [h4]
          rw [pow_succ, pow_mul, pow_two]
          ring
        rw [h3]
        exact h.trans ((Nat.mod_modEq _ _).mul h2)
      · rw [if_neg h1] at h ⊢
        have h3 : acc * b ^ e = acc * (b * b) ^ (e / 2) := by
          have h4 : e = 2 * (e / 2) := by omega
          conv_lhs => rw [h4]
          rw [pow_mul, pow_two]
        rw [h3]
        exact h.trans (h2.mul_left acc)

theorem not_primePow (c fuel : ℕ) (h3 : 3 ≤ c) (hf : c < 2 ^ fuel)
    (hg : Nat.gcd (pm c fuel 1 3 c + c - 3) c = 1) : ¬ IsPrimePow c := by
  intro hpp
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hfact : Fact p.Prime := ⟨hp⟩
  have hpC : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hspec := pm_spec (p ^ k) fuel 1 3 (p ^ k) hf
  rw [one_mul] at hspec
  have hmodp : pm (p ^ k) fuel 1 3 (p ^ k) ≡ 3 ^ (p ^ k) [MOD p] := hspec.of_dvd hpC
  have hz : ((pm (p ^ k) fuel 1 3 (p ^ k) + p ^ k - 3 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodp]
    push_cast
    rw [ZMod.pow_card_pow, ZMod.natCast_self, zero_pow hk.ne']
    ring
  have hdvd : p ∣ pm (p ^ k) fuel 1 3 (p ^ k) + p ^ k - 3 := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have h1 : p ∣ 1 := hg ▸ Nat.dvd_gcd hdvd hpC
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem two_le_card (c : ℕ) (h1 : 1 < c) (h : ¬ IsPrimePow c) : 2 ≤ c.primeFactors.card := by
  have h0 : c.primeFactors.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, Nat.primeFactors_eq_empty]
    omega
  have h1' : c.primeFactors.card ≠ 1 := fun h' => h (isPrimePow_iff_card_primeFactors_eq_one.mpr h')
  omega

theorem card_mul (a b : ℕ) (h : Nat.gcd a b = 1) :
    (a * b).primeFactors.card = a.primeFactors.card + b.primeFactors.card := by
  have hab : Nat.Coprime a b := h
  rw [hab.primeFactors_mul, Finset.card_union_of_disjoint hab.disjoint_primeFactors]

theorem one_le_card (a : ℕ) (h : 1 < a) : 1 ≤ a.primeFactors.card :=
  Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h)

/-- The 1133-digit cofactor of `F_12`. -/
def cof : ℕ := 40386086203521847842442038116961395908045388225743593887534051882867088867451422279926227658353369309602134937818767935489955578234805439581534625494985324713549730074875381338741302421655631135507379857269344735228428553001352597596691638801743636629329355013511352942721273050339170429834278987040381747960884411851433916486144170476008852597093750739127802680309124526032940172579802008470093339990359384991503503614458710698904103258512429909701566697333753540519871100983916899540657050034590964623607736274756781417764221105569531562147057912826327014822324375878810085123801163054580870423717464500275259286644790292287618742984022979008217487409481420224445378839089353872030913057691176817044086502550278535272750787424451118761716552849620868806555149154293300951201837849814408323169458959040706805689440625767829357238882085766112685307073105174963070427573702738362159098805163558648031695168433171835632969724871377060199849541218845177450315677176119955499412825504179204908105894697957170244421770769366517833025139901383316838896066622320648993411213811241118825043233830644947321875736006536117418021434702300430337

theorem hF : Nat.fermatNumber 12 = 114689 * (26017793 * (63766529 * (190274191361 * (1256132134125569 * (568630647535356955169033410940867804839360742060818433 * cof))))) := by decide +kernel

theorem hc1 : Nat.gcd 114689 (26017793 * (63766529 * (190274191361 * (1256132134125569 * (568630647535356955169033410940867804839360742060818433 * cof))))) = 1 := by decide +kernel

theorem hc2 : Nat.gcd 26017793 (63766529 * (190274191361 * (1256132134125569 * (568630647535356955169033410940867804839360742060818433 * cof)))) = 1 := by decide +kernel

theorem hc3 : Nat.gcd 63766529 (190274191361 * (1256132134125569 * (568630647535356955169033410940867804839360742060818433 * cof))) = 1 := by decide +kernel

theorem hc4 : Nat.gcd 190274191361 (1256132134125569 * (568630647535356955169033410940867804839360742060818433 * cof)) = 1 := by decide +kernel

theorem hc5 : Nat.gcd 1256132134125569 (568630647535356955169033410940867804839360742060818433 * cof) = 1 := by decide +kernel

theorem hc6 : Nat.gcd 568630647535356955169033410940867804839360742060818433 cof = 1 := by decide +kernel

theorem hfuel : cof < 2 ^ 3763 := by decide +kernel

theorem hcof3 : 3 ≤ cof := by decide +kernel

theorem hgcd : Nat.gcd (pm cof 3763 1 3 cof + cof - 3) cof = 1 := by decide +kernel

theorem count (F a b c d e f g : ℕ) (hF : F = a * (b * (c * (d * (e * (f * g))))))
    (h1 : Nat.gcd a (b * (c * (d * (e * (f * g))))) = 1)
    (h2 : Nat.gcd b (c * (d * (e * (f * g)))) = 1) (h3 : Nat.gcd c (d * (e * (f * g))) = 1)
    (h4 : Nat.gcd d (e * (f * g)) = 1) (h5 : Nat.gcd e (f * g) = 1) (h6 : Nat.gcd f g = 1)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) (he : 1 < e) (hf : 1 < f)
    (hg : 2 ≤ g.primeFactors.card) : 8 ≤ F.primeFactors.card := by
  subst hF
  rw [card_mul _ _ h1, card_mul _ _ h2, card_mul _ _ h3, card_mul _ _ h4, card_mul _ _ h5,
    card_mul _ _ h6]
  have ha' := one_le_card a ha
  have hb' := one_le_card b hb
  have hc' := one_le_card c hc
  have hd' := one_le_card d hd
  have he' := one_le_card e he
  have hf' := one_le_card f hf
  omega

theorem cof_card : 2 ≤ cof.primeFactors.card :=
  two_le_card cof (lt_of_lt_of_le (by norm_num) hcof3) (not_primePow cof 3763 hcof3 hfuel hgcd)

theorem eight : 8 ≤ (Nat.fermatNumber 12).primeFactors.card :=
  count _ _ _ _ _ _ _ _ hF hc1 hc2 hc3 hc4 hc5 hc6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) cof_card

end F2SelfSeq

theorem OMA.solution : OMA.R_Selfridge_selfridge_seq_conjecture_R1.H1 :=
  F2SelfSeq.eight
