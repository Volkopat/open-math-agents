import OMAStatements.S_mo_357953

/-!
Complete disproof by @connoranderson, linked from statement PR #25446 and desk DONE #116799.
Pinned companion: https://github.com/connoranderson/open-math-agents/blob/f73ccf2e456e6a71a9f6a0e741291cd6c533a8cf/proofs/mo-357953.lean
All mathematical code and the original three-atom counterexample are retained unchanged.
This port adds attribution and current-checker validation; no new counterexample is claimed.
Source: D_809, https://mathoverflow.net/questions/357953 (CC BY-SA 4.0).
There are three independent variables: registered k=1 corresponds to arity k+2=3.
Port and validation: @rodolfoquint.
-/

namespace OMA.S_mo_357953

def atom : Fin 3 → ℚ := ![1/2,-3/5,7/10]
def weight : Fin 3 → ℚ := ![13/39,19/39,7/39]
def signBit : Fin 2 → ℚ := ![1,-1]

noncomputable def triple (x y z : ℚ) : ℝ :=
  let A : ℚ := (1+x)*(1+y)*(1+z)+(1-x)*(1-y)*(1-z)
  let B : ℚ := 1-x*y
  (A:ℝ)*Real.log A - 3*(B:ℝ)*Real.log B

end OMA.S_mo_357953

namespace OMA.S_mo_357953
open Finset

def logCenter (N : ℕ) (q : ℚ) : ℚ :=
  2 * ∑ i ∈ range N, ((q-1)/(q+1))^(2*i+1)/(2*(i:ℚ)+1)

def logError (N : ℕ) (q : ℚ) : ℚ :=
  2 * |(q-1)/(q+1)|^(2*N+1)/(1-((q-1)/(q+1))^2)

lemma log_bounds (N : ℕ) {q : ℚ} (hq : 0<q) :
    ((logCenter N q - logError N q : ℚ):ℝ) ≤ Real.log (q:ℝ) ∧
    Real.log (q:ℝ) ≤ ((logCenter N q + logError N q : ℚ):ℝ) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  let t : ℝ := ((q:ℝ)-1)/(q+1)
  have hpos : (0:ℝ) < q+1 := by linarith
  have ht : |t|<1 := by
    rw [abs_lt]; dsimp [t]
    constructor
    · apply (lt_div_iff₀ hpos).mpr; linarith
    · apply (div_lt_iff₀ hpos).mpr; linarith
  have hn : 1-t ≠ 0 := by linarith [(abs_lt.mp ht).2]
  have he : (1+t)/(1-t) = (q:ℝ) := by
    apply (div_eq_iff hn).mpr
    dsimp [t]
    field_simp
    ring
  have h := Real.sum_range_sub_log_div_le ht N
  rw [he,abs_le] at h
  simp only [logCenter,logError]
  push_cast
  change 2 * _ - 2 * |t|^(2*N+1)/(1-t^2) ≤ _ ∧ _ ≤ 2 * _ + 2 * |t|^(2*N+1)/(1-t^2)
  rw [mul_div_assoc (2:ℝ) (|t|^(2*N+1)) (1-t^2)]
  constructor <;> linarith only [h.1,h.2]

end OMA.S_mo_357953

namespace OMA.S_mo_357953

open Finset

/-- Logarithms rounded to ten decimal places at all arguments of the finite expectations. -/
private def logTable : List (ℚ × ℤ) := [
  (51/100, -6733445533), (29/50, -5447271754), (16/25, -4462871026), (13/20, -4307829161),
  (7/10, -3566749439), (3/4, -2876820725), (51/50, 198026273), (26/25, 392207132),
  (53/50, 582689081), (11/10, 953101798), (5/4, 2231435513), (63/50, 2311117210),
  (32/25, 2468600779), (13/10, 2623642645), (27/20, 3001045925), (34/25, 3074846997),
  (71/50, 3506568716), (149/100, 3987761200), (3/2, 4054651081), (38/25, 4187103349),
  (77/50, 4317824164), (79/50, 4574248470), (7/2, 12527629685), (37/10, 13083328197),
  (39/10, 13609765531), (98/25, 13660916538), (207/50, 14206957878), (104/25, 14255150743),
  (219/50, 14770487244), (22/5, 14816045409), (233/50, 15390154481), (247/50, 15973653312)]

private def logKeys : List ℚ := logTable.map Prod.fst
private def logMid (q : ℚ) : ℚ := ((logTable.lookup q).getD 0 : ℤ)/ (10^10 : ℚ)
private def radius : ℚ := 1/10^9

private def checkLog (q : ℚ) : Bool := decide
    (0 < q ∧ logMid q - radius ≤ logCenter 28 q - logError 28 q ∧
     logCenter 28 q + logError 28 q ≤ logMid q + radius)

private lemma checked_logs : logKeys.all checkLog = true := by decide +kernel

private lemma boundLog {q : ℚ} (hq : q ∈ logKeys) :
    0 < q ∧ ((logMid q-radius : ℚ):ℝ) ≤ Real.log (q:ℝ) ∧
      Real.log (q:ℝ) ≤ ((logMid q+radius : ℚ):ℝ) := by
  have h := List.all_eq_true.mp checked_logs q hq
  obtain ⟨hp,hl,hu⟩ := of_decide_eq_true h
  obtain ⟨h₁,h₂⟩ := log_bounds 28 hp
  exact ⟨hp,le_trans (by exact_mod_cast hl) h₁, le_trans h₂ (by exact_mod_cast hu)⟩

private def factorA (x y z : ℚ) := (1+x)*(1+y)*(1+z)+(1-x)*(1-y)*(1-z)
private def factorB (x y : ℚ) := 1-x*y

private def tripleLo (x y z : ℚ) :=
  let A := factorA x y z
  let B := factorB x y
  A*(logMid A-radius) - 3*B*(logMid B+radius)

private def tripleHi (x y z : ℚ) :=
  let A := factorA x y z
  let B := factorB x y
  A*(logMid A+radius) - 3*B*(logMid B-radius)

private lemma boundTriple (x y z : ℚ) (hA : factorA x y z ∈ logKeys) (hB : factorB x y ∈ logKeys) :
    (tripleLo x y z : ℝ) ≤ triple x y z ∧ triple x y z ≤ (tripleHi x y z:ℝ) := by
  obtain ⟨ha,al,au⟩ := boundLog hA
  obtain ⟨hb,bl,bu⟩ := boundLog hB
  have ha' : 0 ≤ (factorA x y z : ℝ) := by exact_mod_cast ha.le
  have hb' : 0 ≤ 3*(factorB x y : ℝ) := by positivity
  change _ ≤ (factorA x y z : ℝ)*Real.log (factorA x y z) -
    3*(factorB x y:ℝ)*Real.log (factorB x y) ∧ _ ≤ _
  simp only [tripleLo,tripleHi,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
  simp only [Rat.cast_sub] at al bl
  constructor
  · exact sub_le_sub (mul_le_mul_of_nonneg_left al ha') (mul_le_mul_of_nonneg_left bu hb')
  · exact sub_le_sub (mul_le_mul_of_nonneg_left au ha') (mul_le_mul_of_nonneg_left bl hb')

private def signedAtom (s : Fin 2) (i : Fin 3) := signBit s * atom i

private lemma keys_ok : ∀ (a b c : Fin 2) (i j k : Fin 3),
    factorA (signedAtom a i) (signedAtom b j) (signedAtom c k) ∈ logKeys ∧
      factorB (signedAtom a i) (signedAtom b j) ∈ logKeys := by decide +kernel

private def approxAvg (F : ℚ → ℚ → ℚ → ℚ) (a b c : Fin 2) : ℚ :=
  ∑ i, ∑ j, ∑ k, weight i * weight j * weight k * F (signedAtom a i) (signedAtom b j) (signedAtom c k)

private noncomputable def realAvg (a b c : Fin 2) : ℝ :=
  ∑ i, ∑ j, ∑ k, (weight i : ℝ) * (weight j : ℝ) * (weight k : ℝ) *
    triple (signedAtom a i) (signedAtom b j) (signedAtom c k)

private lemma boundAvg (a b c : Fin 2) :
    (approxAvg tripleLo a b c : ℝ) ≤ realAvg a b c ∧ realAvg a b c ≤ (approxAvg tripleHi a b c:ℝ) := by
  have hw (i : Fin 3) : 0 ≤ (weight i:ℝ) := by fin_cases i <;> norm_num [weight]
  simp only [approxAvg, realAvg, Rat.cast_sum, Rat.cast_mul]
  constructor <;> apply sum_le_sum <;> intro i _ <;> apply sum_le_sum <;> intro j _ <;>
    apply sum_le_sum <;> intro k _ <;> apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (hw i) (hw j)) (hw k))
  · exact (boundTriple _ _ _ (keys_ok a b c i j k).1 (keys_ok a b c i j k).2).1
  · exact (boundTriple _ _ _ (keys_ok a b c i j k).1 (keys_ok a b c i j k).2).2

private lemma rational_gap :
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, approxAvg tripleHi a b c)/8 <
      approxAvg tripleLo 0 0 0 := by decide +kernel

lemma bad_triple :
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2,
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (weight i : ℝ) * (weight j : ℝ) * (weight k : ℝ) *
          triple (signBit a * atom i) (signBit b * atom j) (signBit c * atom k))/8 <
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (weight i : ℝ) * (weight j : ℝ) * (weight k : ℝ) *
        triple (atom i) (atom j) (atom k)
 := by
  have upper : (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, realAvg a b c)/8 ≤
      (((∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, approxAvg tripleHi a b c)/8 : ℚ):ℝ) := by
    push_cast
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => (boundAvg a b c).2
  have strict : (((∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, approxAvg tripleHi a b c)/8 : ℚ):ℝ)
       < (approxAvg tripleLo 0 0 0 : ℝ) := by exact_mod_cast rational_gap
  have hr := (upper.trans_lt strict).trans_le (boundAvg 0 0 0).1
  simpa only [realAvg,signedAtom,show signBit 0 = 1 by rfl,one_mul] using hr

end OMA.S_mo_357953

namespace OMA.S_mo_357953
open MeasureTheory Finset

private lemma weight_nonneg (i : Fin 3) : 0 ≤ (weight i : ℝ) := by
  fin_cases i <;> norm_num [weight]

private noncomputable def testLaw : Measure (Fin 3) :=
  ∑ i : Fin 3, ENNReal.ofReal (weight i) • Measure.dirac i

private instance : IsProbabilityMeasure testLaw := by
  constructor
  simp only [testLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonneg i)]
  norm_num [weight, Fin.sum_univ_succ]

private lemma testLaw_single (i : Fin 3) : testLaw {i} = ENNReal.ofReal (weight i) := by
  classical
  simp [testLaw, Set.indicator_apply]

private lemma atom_mean : (∫ i : Fin 3, (atom i : ℝ) ∂testLaw) = 0 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, testLaw_single, ENNReal.toReal_ofReal (weight_nonneg _), smul_eq_mul]
  norm_num [Fin.sum_univ_succ, weight, atom]

private lemma sum_three {α : Type} [Fintype α] (f : (Fin 3 → α) → ℝ) :
    (∑ w, f w) = ∑ i : α, ∑ j : α, ∑ k : α, f ![i,j,k] := by
  classical
  let e : (α × α × α) ≃ (Fin 3 → α) :=
    { toFun := fun a => ![a.1, a.2.1, a.2.2]
      invFun := fun w => (w 0, w 1, w 2)
      left_inv := by intro a; rfl
      right_inv := by intro w; funext j; fin_cases j <;> rfl }
  rw [← e.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private lemma triple_integral (f : (Fin 3 → Fin 3) → ℝ) :
    (∫ w, f w ∂Measure.pi (fun _ : Fin 3 => testLaw)) =
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (weight i:ℝ) * (weight j:ℝ) * (weight k:ℝ) * f ![i,j,k] := by
  rw [integral_fintype Integrable.of_finite, sum_three]
  simp [measureReal_def, testLaw_single, ENNReal.toReal_ofReal (weight_nonneg _),
    Fin.prod_univ_three, mul_assoc]

private lemma stat_triple (t : Fin 3 → ℚ) :
    statistic (k:=1) (fun i => (t i:ℝ)) = triple (t 0) (t 1) (t 2) := by
  simp [statistic, triple, Fin.prod_univ_three]

private lemma sign_cast (i : Fin 2) : ((signBit i:ℚ):ℝ) = signReal i := by
  fin_cases i <;> norm_num [signBit, signReal]

private lemma orig_atoms : original 1 testLaw (fun i => (atom i:ℝ)) =
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (weight i:ℝ)*(weight j:ℝ)*(weight k:ℝ) *
      triple (atom i) (atom j) (atom k) := by
  unfold original
  rw [triple_integral]
  simp [stat_triple]

private lemma sym_atoms : symmetrized 1 testLaw (fun i => (atom i:ℝ)) =
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (weight i:ℝ)*(weight j:ℝ)*(weight k:ℝ) *
        triple (signBit a*atom i) (signBit b*atom j) (signBit c*atom k))/8 := by
  have hstat (b : Fin 3 → Fin 2) (w : Fin 3 → Fin 3) :
      statistic (k:=1) (fun i => signReal (b i) * (atom (w i):ℝ)) =
      triple (signBit (b 0)*atom (w 0)) (signBit (b 1)*atom (w 1)) (signBit (b 2)*atom (w 2)) := by
    simpa [sign_cast] using stat_triple (fun i => signBit (b i)*atom (w i))
  have hsum (b : Fin 3 → Fin 2) := triple_integral
    (fun w : Fin 3 → Fin 3 => statistic (k:=1) (fun i => signReal (b i)*(atom (w i):ℝ)))
  change (∑ b : Fin 3 → Fin 2, ∫ w : Fin 3 → Fin 3,
    statistic (k:=1) (fun i => signReal (b i)*(atom (w i):ℝ)) ∂Measure.pi (fun _ : Fin 3 => testLaw))
    / (2:ℝ)^3 = _
  simp_rw [hsum]
  rw [sum_three]
  simp only [hstat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

end OMA.S_mo_357953

open OMA.S_mo_357953 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_357953.main) := by
  intro h
  have hh := h 1 (Fin 3) testLaw (fun i => (atom i:ℝ)) (measurable_of_finite _)
      (Filter.Eventually.of_forall (fun i => by fin_cases i <;> norm_num [atom])) atom_mean
  rw [orig_atoms, sym_atoms] at hh
  exact (not_lt_of_ge hh) bad_triple
