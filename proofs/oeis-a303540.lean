import OMAStatements.S_oeis_a303540

namespace SunCertificate

def witness : ℕ := 210107364447

/-- An efficient evaluator for the central binomial coefficients. -/
private def central : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * (2 * k + 1) * central k / (k + 1)

private theorem central_correct (k : ℕ) : central k = Nat.centralBinom k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [central, ih, ← Nat.succ_mul_centralBinom_succ]
    exact Nat.mul_div_cancel_left _ (Nat.succ_pos k)

private def forbidden (t : ℕ) : Bool :=
  t % 4 == 3 || t % 8 == 6 || t % 16 == 12 || t == 24

private def primes : List ℕ :=
  [3, 7, 11, 19, 23, 31, 43, 59, 67, 71, 107, 179, 191, 1019, 1511,
   1831, 2011, 2447, 3907, 7699, 23027, 24223, 24379]

private def blocked (r : ℕ) : Bool :=
  forbidden (r % 32) || primes.any (fun p => [0,1,2,3].any (fun j : ℕ =>
    decide (p ^ (2*j+1) ∣ r ∧ ¬p ^ (2*j+2) ∣ r)))

private theorem squares_mod_32 (a b : ℕ) :
    forbidden ((a^2+b^2)%32) = false := by
  have tab : ∀ i j : Fin 32, forbidden ((i.val^2+j.val^2)%32) = false := by decide
  have hm : ((a%32)^2+(b%32)^2)%32 = (a^2+b^2)%32 :=
    ((Nat.mod_modEq a 32).pow 2).add ((Nat.mod_modEq b 32).pow 2)
  rw [← hm]
  exact tab ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩

private theorem primes_valid : ∀ p ∈ primes, Nat.Prime p ∧ p % 4 = 3 := by
  norm_num [primes]

private theorem blocked_sound {r : ℕ} (hr : blocked r = true) :
    ¬ ∃ a b : ℕ, r = a^2+b^2 := by
  rintro ⟨a,b,hab⟩
  have htwo : forbidden (r%32) = false := by
    rw [hab]
    exact squares_mod_32 a b
  simp only [blocked, htwo, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at hr
  obtain ⟨p,hp,j,_,hd,hn⟩ := hr
  obtain ⟨hprime,hfour⟩ := primes_valid p hp
  have hpos : r ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  have hdvd : p ∣ r := dvd_trans (dvd_pow_self p (by omega : 2*j+1 ≠ 0)) hd
  have heven := Nat.eq_sq_add_sq_iff.mp ⟨a,b,hab⟩ p
    (Nat.mem_primeFactors.mpr ⟨hprime,hdvd,hpos⟩) hfour
  have hlo := (padicValNat_dvd_iff_le_of_ne_one hprime.ne_one hpos).mp hd
  have hhi : ¬ 2*j+2 ≤ padicValNat p r :=
    fun h => hn ((padicValNat_dvd_iff_le_of_ne_one hprime.ne_one hpos).mpr h)
  obtain ⟨m,hm⟩ := heven
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem all_pairs :
    ∀ c d : Fin 21, witness < central c.val + central d.val ∨
      blocked (witness - central c.val - central d.val) = true := by decide

private theorem index_bound (k : ℕ) (h : Nat.centralBinom k ≤ witness) : k < 21 := by
  by_contra! ge
  have hbig : witness < central 21 := by decide
  rw [central_correct] at hbig
  exact (Nat.not_lt_of_ge ((Nat.centralBinom_strictMono.monotone ge).trans h)) hbig

theorem no_representation (a b c d : ℕ) :
    a^2+b^2+(2*c).choose c+(2*d).choose d ≠ witness := by
  intro h
  change a^2+b^2+Nat.centralBinom c+Nat.centralBinom d = witness at h
  have hc := index_bound c (by omega)
  have hd := index_bound d (by omega)
  have hh := all_pairs ⟨c,hc⟩ ⟨d,hd⟩
  change witness < central c + central d ∨ blocked (witness-central c-central d) = true at hh
  simp only [central_correct] at hh
  rcases hh with hover | hblock
  · omega
  · exact blocked_sound hblock ⟨a,b,by omega⟩

end SunCertificate

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a303540.main) := by
  intro h
  obtain ⟨a,b,c,d,hab⟩ := h SunCertificate.witness (by decide)
  exact SunCertificate.no_representation a b c d hab

