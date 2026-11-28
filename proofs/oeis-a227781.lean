import OMAStatements.S_oeis_a227781
import Mathlib

/-!
For every positive modulus, classify when representing minus one requires exactly
three or exactly four squares. The upper bound for three terms comes from doubling
a two-term representation at half the modulus.
-/

open OMA.S_oeis_a227781

lemma oma_minus_one_two_squares (n : ℕ) (hn : 0 < n) (hfour : ¬ 4 ∣ n) :
    Represents n 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k*(n : ℤ)-1)%4 = 1 := by
    by_cases even : n % 2 = 0
    · refine ⟨1, ?_⟩
      simp only [one_mul]
      omega
    · exact ⟨2, by omega⟩
  let r : ℤ := k*n - 1
  have rr : r % 4 = 1 := hk
  have cop4 : IsCoprime r 4 := ⟨1, -(r/4), by omega⟩
  have copn : IsCoprime r (n : ℤ) := ⟨-1,k,by dsimp [r]; ring⟩
  have cop : IsCoprime r ((4*n : ℕ) : ℤ) := by exact_mod_cast cop4.mul_right copn
  obtain ⟨p,_,hp,heq⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (q := 4*n) (a := r)
    (by positivity) cop
  have heq' : (p : ℤ) ≡ r [ZMOD 4 * (n : ℤ)] := by exact_mod_cast heq
  have hp4 : (p : ℤ) ≡ r [ZMOD 4] := Int.ModEq.of_dvd (dvd_mul_right _ _) heq'
  change (p : ℤ) % 4 = r % 4 at hp4
  have hpn : (p : ℤ) ≡ r [ZMOD (n : ℤ)] := Int.ModEq.of_dvd (dvd_mul_left _ _) heq'
  obtain ⟨m,hm⟩ := Int.modEq_iff_dvd.mp hpn.symm
  have hplus : (n : ℤ) ∣ p + 1 := by
    refine ⟨m+k,?_⟩
    dsimp [r] at hm
    linear_combination hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  refine ⟨[(a : ℤ), (b : ℤ)],rfl,?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have ht : (a : ℤ)^2 + (b : ℤ)^2 = (p : ℤ) := by exact_mod_cast hab
  rwa [ht]

lemma oma_least_four_bound {n k : ℕ} (hn : 8 ∣ n) (hr : Represents n k) : 4 ≤ k := by
  have impossible (a b c : ℤ) : ¬ (8:ℤ) ∣ a^2 + b^2 + c^2 + 1 := by
    intro d
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr d
    push_cast at z
    have residues : ∀ x y w : ZMod 8, x^2 + y^2 + w^2 + 1 ≠ 0 := by decide
    exact residues _ _ _ z
  obtain ⟨xs,rfl,h⟩ := hr
  have d : (8:ℤ) ∣ (xs.map (fun x => x^2)).sum + 1 := dvd_trans (by exact_mod_cast hn) h
  match xs with
  | [] => simp at d
  | [a] => exact False.elim (impossible a 0 0 (by simpa using d))
  | [a,b] => exact False.elim (impossible a b 0 (by simpa using d))
  | [a,b,c] => exact False.elim (impossible a b c (by simpa [add_assoc] using d))
  | _ :: _ :: _ :: _ :: _ => simp

lemma oma_least_three_bound {n k : ℕ} (hn : 4 ∣ n) (hr : Represents n k) : 3 ≤ k := by
  have impossible (a b : ℤ) : ¬ (4:ℤ) ∣ a^2 + b^2 + 1 := by
    intro d
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr d
    push_cast at z
    have residues : ∀ x y : ZMod 4, x^2 + y^2 + 1 ≠ 0 := by decide
    exact residues _ _ z
  obtain ⟨xs,rfl,h⟩ := hr
  have d : (4:ℤ) ∣ (xs.map (fun x => x^2)).sum + 1 := dvd_trans (by exact_mod_cast hn) h
  match xs with
  | [] => simp at d
  | [a] => exact False.elim (impossible a 0 (by simpa using d))
  | [a,b] => exact False.elim (impossible a b (by simpa using d))
  | _ :: _ :: _ :: _ => simp

private theorem oma_four_squares_upper (n : ℕ) (hn : 0 < n) : Represents n 4 := by
  obtain ⟨a,b,c,d,hs⟩ := Nat.sum_four_squares (n-1)
  refine ⟨[a,b,c,d],rfl,?_⟩
  have ht : a^2+b^2+c^2+d^2+1=n := by omega
  have hz : (a : ℤ)^2+b^2+c^2+d^2+1=n := by exact_mod_cast ht
  refine ⟨1, ?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one]
  linarith

/-- Doubling a modulus and a two-square representation produces three squares. -/
private theorem oma_twice_two_squares (m : ℕ) (h : Represents m 2) : Represents (2*m) 3 := by
  obtain ⟨xs,hlen,hs⟩ := h
  match xs with
  | [x,y] =>
    obtain ⟨v,hv⟩ := hs
    refine ⟨[x+y,x-y,1],rfl,v,?_⟩
    simp at hv ⊢
    nlinarith
  | [] | [_] | _ :: _ :: _ :: _ => simp at hlen

theorem oma_minus_one_finish
    (two : ∀ n : ℕ, 0 < n → ¬ 4 ∣ n → Represents n 2)
    (fourBound : ∀ n k : ℕ, 8 ∣ n → Represents n k → 4 ≤ k)
    (threeBound : ∀ n k : ℕ, 4 ∣ n → Represents n k → 3 ≤ k) :
    type_of% @OMA.S_oeis_a227781.main := by
  intro n hn
  have caseThree (h : n%8=4) : Represents n 3 := by
    have hm := two (n/2) (by omega) (by omega)
    convert oma_twice_two_squares (n/2) hm using 1
    omega
  constructor
  · constructor
    · intro h
      by_contra hn8
      by_cases h4 : 4 ∣ n
      · have bad := h.2 (caseThree (by omega))
        omega
      · have bad := h.2 (two n hn h4)
        omega
    · intro hn8
      exact ⟨oma_four_squares_upper n hn, fun k hk => fourBound n k hn8 hk⟩
  · constructor
    · intro h
      by_cases h8 : 8 ∣ n
      · have bad := fourBound n 3 h8 h.1
        omega
      · by_contra hmod
        have bad := h.2 (two n hn (by omega))
        omega
    · intro hmod
      exact ⟨caseThree hmod, fun k hk => threeBound n k (by omega) hk⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a227781.main :=
  oma_minus_one_finish oma_minus_one_two_squares
    (fun _ _ => oma_least_four_bound) (fun _ _ => oma_least_three_bound)
