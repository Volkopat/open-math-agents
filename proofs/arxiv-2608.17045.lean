import OMAStatements.S_arxiv_2608_17045

/-!
# A counterexample to the geodesic half-capacity conjectures

Two consecutive highly composite numbers lose both 613 and 617. The step removing the second
prime halves a divisor count that is already strictly below the original record.

The pair occurs at entries 5856 and 5857 in Achim Flammenkamp's table. The record certificate
below proves consecutiveness directly by enumerating prime-exponent profiles.

Source: https://arxiv.org/html/2608.17045v1#S9
Table: https://wwwhomes.uni-bielefeld.de/achim/HCN/
-/


namespace HCN

def profileValue (ps es : List ℕ) : ℕ := (ps.zipWith (· ^ ·) es).prod
def profileTau (es : List ℕ) : ℕ := (es.map (·+1)).prod

structure ScoreRow where
  prime : ℕ
  center : ℕ
  weights : List ℕ

def scoreScale : ℕ := 4096
def scoreCap : ℕ := 11881

def recordH : ℕ := 1762535618477653737991840481952590966940651576262747381115049225782332306991616654181274539986256419497891273105711480786681542326823308639709118428296671978001593393879999346121727760662167556589494782061440942321807359059167629420142673670539182759175140828668887502743222400000

def recordK : ℕ := 1853461935315196561380677149180911352188304682319056984100712680438789012218346597344277632277017212806456780950553573824385881635250157052452663543320002264528178353421399139474444631804933508058775716458596106573381546712657697268622635968044679350217080627941856479019064320000

def countH : ℕ := 78069428453607717662223843870029905920

def countK : ℕ := 78596175307520553825427768952959795200

/-- Each row stores a prime, the exponent maximizing the local score, and integer lower bounds on
its score loss at successive exponents. The scale is 4096. -/
def scoreRows : List ScoreRow := [
  ⟨2, 12, [11882, 11882, 11882, 11882, 11882, 11882, 11882, 11882, 11882, 11882, 7735, 4948, 4096, 4223, 5261, 7730, 11882]⟩,
  ⟨3, 7, [11882, 11882, 11882, 11882, 11882, 11882, 7072, 4096, 4248, 6976, 11882]⟩,
  ⟨5, 5, [11882, 11882, 11882, 11882, 5574, 4096, 8535, 11882]⟩,
  ⟨7, 4, [11882, 11882, 11882, 6571, 4096, 11562, 11882]⟩,
  ⟨11, 3, [11882, 11882, 11736, 4096, 11882]⟩,
  ⟨13, 3, [11882, 11882, 6016, 4096, 11882]⟩,
  ⟨17, 2, [11882, 11882, 4096, 8154, 11882]⟩,
  ⟨19, 2, [11882, 11882, 4096, 11882]⟩,
  ⟨23, 2, [11882, 11882, 4096, 11882]⟩,
  ⟨29, 2, [11882, 11882, 4096, 11882]⟩,
  ⟨31, 2, [11882, 11882, 4096, 11882]⟩,
  ⟨37, 2, [11882, 7160, 4096, 11882]⟩,
  ⟨41, 2, [11882, 4748, 4096, 11882]⟩,
  ⟨43, 1, [11882, 4096, 4274, 11882]⟩,
  ⟨47, 1, [11882, 4096, 6100, 11882]⟩,
  ⟨53, 1, [11882, 4096, 9864, 11882]⟩,
  ⟨59, 1, [11882, 4096, 11882]⟩,
  ⟨61, 1, [11882, 4096, 11882]⟩,
  ⟨67, 1, [11882, 4096, 11882]⟩,
  ⟨71, 1, [11882, 4096, 11882]⟩,
  ⟨73, 1, [11882, 4096, 11882]⟩,
  ⟨79, 1, [11882, 4096, 11882]⟩,
  ⟨83, 1, [11882, 4096, 11882]⟩,
  ⟨89, 1, [11882, 4096, 11882]⟩,
  ⟨97, 1, [11882, 4096, 11882]⟩,
  ⟨101, 1, [11882, 4096, 11882]⟩,
  ⟨103, 1, [11882, 4096, 11882]⟩,
  ⟨107, 1, [11882, 4096, 11882]⟩,
  ⟨109, 1, [11882, 4096, 11882]⟩,
  ⟨113, 1, [11882, 4096, 11882]⟩,
  ⟨127, 1, [11882, 4096, 11882]⟩,
  ⟨131, 1, [11882, 4096, 11882]⟩,
  ⟨137, 1, [11882, 4096, 11882]⟩,
  ⟨139, 1, [11882, 4096, 11882]⟩,
  ⟨149, 1, [11882, 4096, 11882]⟩,
  ⟨151, 1, [11882, 4096, 11882]⟩,
  ⟨157, 1, [11882, 4096, 11882]⟩,
  ⟨163, 1, [11882, 4096, 11882]⟩,
  ⟨167, 1, [11882, 4096, 11882]⟩,
  ⟨173, 1, [11882, 4096, 11882]⟩,
  ⟨179, 1, [11882, 4096, 11882]⟩,
  ⟨181, 1, [11882, 4096, 11882]⟩,
  ⟨191, 1, [11882, 4096, 11882]⟩,
  ⟨193, 1, [11882, 4096, 11882]⟩,
  ⟨197, 1, [11882, 4096, 11882]⟩,
  ⟨199, 1, [11882, 4096, 11882]⟩,
  ⟨211, 1, [11882, 4096, 11882]⟩,
  ⟨223, 1, [11882, 4096, 11882]⟩,
  ⟨227, 1, [11882, 4096, 11882]⟩,
  ⟨229, 1, [11882, 4096, 11882]⟩,
  ⟨233, 1, [11882, 4096, 11882]⟩,
  ⟨239, 1, [11882, 4096, 11882]⟩,
  ⟨241, 1, [11882, 4096, 11882]⟩,
  ⟨251, 1, [11882, 4096, 11882]⟩,
  ⟨257, 1, [11882, 4096, 11882]⟩,
  ⟨263, 1, [11882, 4096, 11882]⟩,
  ⟨269, 1, [11882, 4096, 11882]⟩,
  ⟨271, 1, [11882, 4096, 11882]⟩,
  ⟨277, 1, [11882, 4096, 11882]⟩,
  ⟨281, 1, [11882, 4096, 11882]⟩,
  ⟨283, 1, [11882, 4096, 11882]⟩,
  ⟨293, 1, [11882, 4096, 11882]⟩,
  ⟨307, 1, [11882, 4096, 11882]⟩,
  ⟨311, 1, [11882, 4096, 11882]⟩,
  ⟨313, 1, [11882, 4096, 11882]⟩,
  ⟨317, 1, [11882, 4096, 11882]⟩,
  ⟨331, 1, [11882, 4096, 11882]⟩,
  ⟨337, 1, [11882, 4096, 11882]⟩,
  ⟨347, 1, [11882, 4096, 11882]⟩,
  ⟨349, 1, [11882, 4096, 11882]⟩,
  ⟨353, 1, [11882, 4096, 11882]⟩,
  ⟨359, 1, [11882, 4096, 11882]⟩,
  ⟨367, 1, [11882, 4096, 11882]⟩,
  ⟨373, 1, [11882, 4096, 11882]⟩,
  ⟨379, 1, [11882, 4096, 11882]⟩,
  ⟨383, 1, [11882, 4096, 11882]⟩,
  ⟨389, 1, [11882, 4096, 11882]⟩,
  ⟨397, 1, [11882, 4096, 11882]⟩,
  ⟨401, 1, [11882, 4096, 11882]⟩,
  ⟨409, 1, [11882, 4096, 11882]⟩,
  ⟨419, 1, [11882, 4096, 11882]⟩,
  ⟨421, 1, [11882, 4096, 11882]⟩,
  ⟨431, 1, [11882, 4096, 11882]⟩,
  ⟨433, 1, [11882, 4096, 11882]⟩,
  ⟨439, 1, [11882, 4096, 11882]⟩,
  ⟨443, 1, [11882, 4096, 11882]⟩,
  ⟨449, 1, [11882, 4096, 11882]⟩,
  ⟨457, 1, [11882, 4096, 11882]⟩,
  ⟨461, 1, [11882, 4096, 11882]⟩,
  ⟨463, 1, [11882, 4096, 11882]⟩,
  ⟨467, 1, [11835, 4096, 11882]⟩,
  ⟨479, 1, [10693, 4096, 11882]⟩,
  ⟨487, 1, [10008, 4096, 11882]⟩,
  ⟨491, 1, [9685, 4096, 11882]⟩,
  ⟨499, 1, [9079, 4096, 11882]⟩,
  ⟨503, 1, [8794, 4096, 11882]⟩,
  ⟨509, 1, [8386, 4096, 11882]⟩,
  ⟨521, 1, [7640, 4096, 11882]⟩,
  ⟨523, 1, [7524, 4096, 11882]⟩,
  ⟨541, 1, [6571, 4096, 11882]⟩,
  ⟨547, 1, [6288, 4096, 11882]⟩,
  ⟨557, 1, [5848, 4096, 11882]⟩,
  ⟨563, 1, [5603, 4096, 11882]⟩,
  ⟨569, 1, [5370, 4096, 11882]⟩,
  ⟨571, 1, [5295, 4096, 11882]⟩,
  ⟨577, 1, [5078, 4096, 11882]⟩,
  ⟨587, 1, [4741, 4096, 11882]⟩,
  ⟨593, 1, [4552, 4096, 11882]⟩,
  ⟨599, 1, [4372, 4096, 11882]⟩,
  ⟨601, 1, [4314, 4096, 11882]⟩,
  ⟨607, 1, [4146, 4096, 11882]⟩,
  ⟨613, 0, [4096, 4208, 11882]⟩,
  ⟨617, 0, [4096, 4319, 11882]⟩,
  ⟨619, 0, [4096, 4375, 11882]⟩,
  ⟨631, 0, [4096, 4724, 11882]⟩,
  ⟨641, 0, [4096, 5031, 11882]⟩,
  ⟨643, 0, [4096, 5094, 11882]⟩,
  ⟨647, 0, [4096, 5222, 11882]⟩,
  ⟨653, 0, [4096, 5418, 11882]⟩,
  ⟨659, 0, [4096, 5620, 11882]⟩,
  ⟨661, 0, [4096, 5689, 11882]⟩
]

def scorePrimes : List ℕ := scoreRows.map ScoreRow.prime

end HCN

namespace HCN

def rowWeight (r : ScoreRow) (e : ℕ) := r.weights[e]?.getD (scoreCap+1)
def denom (r : ScoreRow) (e : ℕ) := (e+1)^37 * (r.prime^r.center)^4
def numer (r : ScoreRow) (e : ℕ) := (r.center+1)^37 * (r.prime^e)^4
def rowBound (r : ScoreRow) (e : ℕ) : Bool :=
  decide (scoreScale ≤ rowWeight r e ∧ rowWeight r e * denom r e ≤ scoreScale * numer r e)

/-- Check the tabulated lower bounds and the one-step slope from which later losses increase. -/
def rowGood (r : ScoreRow) : Bool :=
  decide (0 < r.prime ∧ (r.weights.length+2)^37 ≤ r.prime^4*(r.weights.length+1)^37) &&
    (List.range (r.weights.length+1)).all (rowBound r)

def costStep (c : ℕ) (r : ScoreRow) (e : ℕ) := c * rowWeight r e / scoreScale

def finalCost (c : ℕ) : List ScoreRow → List ℕ → ℕ
  | [], _ => c
  | r :: rs, [] => finalCost (costStep c r 0) rs []
  | r :: rs, e :: es => finalCost (costStep c r e) rs es

def baseCount (rs : List ScoreRow) := profileTau (rs.map ScoreRow.center)
def baseValue (rs : List ScoreRow) := profileValue (rs.map ScoreRow.prime) (rs.map ScoreRow.center)

def recordOK (v d : ℕ) : Bool :=
  decide ((countH ≤ d → recordH ≤ v) ∧ (countH < d → recordK ≤ v))

/-- Check each feasible positive exponent prefix. A prefix may stop at any prime. Its divisor count
and integer value are tested before extending it by the next prime. -/
def searchRows : List ScoreRow → ℕ → ℕ → ℕ → Bool
  | [], c, v, d => decide (scoreCap < c ∨ recordK < v) || recordOK v d
  | r :: rs, c, v, d =>
    decide (scoreCap < c ∨ recordK < v) ||
    (recordOK v d && ((List.range r.weights.length).all fun j =>
      let e := j+1
      let cost := costStep c r e
      decide (scoreCap < cost) || searchRows rs cost (v*r.prime^e) (d*(e+1))))

end HCN

namespace HCN

private theorem step_growth {p q e t : ℕ} (h : (q+2)^t ≤ p^4*(q+1)^t) (he : q ≤ e) :
    (e+2)^t ≤ p^4*(e+1)^t := by
  have hh : (e+2)*(q+1) ≤ (q+2)*(e+1) := by nlinarith only [he]
  have hh' := Nat.pow_le_pow_left hh t
  rw [Nat.mul_pow, Nat.mul_pow] at hh'
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos (Nat.succ_pos q) : 0 < (q+1)^t)
  calc
    _ ≤ _ := hh'
    _ ≤ (p^4*(q+1)^t)*(e+1)^t := Nat.mul_le_mul_right _ h
    _ = _ := by simp only [Nat.mul_comm, Nat.mul_left_comm]

private theorem all_weights {r : ScoreRow} (h : rowGood r = true) (e : ℕ) :
    scoreScale ≤ rowWeight r e ∧ rowWeight r e * denom r e ≤ scoreScale * numer r e := by
  obtain ⟨hh,hr⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨_,hg⟩ := of_decide_eq_true hh
  have hpre (j : ℕ) (hj : j ≤ r.weights.length) :
      scoreScale ≤ rowWeight r j ∧ rowWeight r j * denom r j ≤ scoreScale * numer r j :=
    of_decide_eq_true (List.all_eq_true.mp hr _ (List.mem_range.mpr (by omega)))
  by_cases he : e ≤ r.weights.length
  · exact hpre _ he
  · have qle : r.weights.length ≤ e := by omega
    have hout (t : ℕ) (ht : r.weights.length ≤ t) : rowWeight r t = scoreCap + 1 := by
      simp [rowWeight, List.getElem?_eq_none ht]
    rw [hout e qle]
    refine ⟨by decide, ?_⟩
    clear he
    induction e, qle using Nat.le_induction with
    | base =>
      have hbase := (hpre _ le_rfl).2
      simpa only [hout _ le_rfl] using hbase
    | succ e hqe ih =>
      have hstep := step_growth hg hqe
      change (scoreCap+1)*((e+2)^37 * (r.prime^r.center)^4) ≤
        scoreScale*((r.center+1)^37*(r.prime^(e+1))^4)
      calc
        _ ≤ (scoreCap+1)*((r.prime^4*(e+1)^37)*(r.prime^r.center)^4) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hstep)
        _ = ((scoreCap+1)*denom r e)*r.prime^4 := by simp only [denom, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (scoreScale * numer r e)*r.prime^4 := Nat.mul_le_mul_right _ ih
        _ = _ := by simp only [numer, pow_succ r.prime e, Nat.mul_pow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

private theorem step_lower {r : ScoreRow} (h : rowGood r = true) (c e : ℕ) :
    c ≤ costStep c r e :=
  (Nat.le_div_iff_mul_le (by decide : 0 < scoreScale)).mpr
    (Nat.mul_le_mul_left _ (all_weights h e).1)

private theorem step_upper {r : ScoreRow} (h : rowGood r = true) (c e : ℕ) :
    costStep c r e * denom r e ≤ c * numer r e := by
  refine Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < scoreScale)
  calc
    _ = (costStep c r e * scoreScale)*denom r e := by ac_rfl
    _ ≤ (c*rowWeight r e)*denom r e :=
      Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ = c*(rowWeight r e*denom r e) := Nat.mul_assoc _ _ _
    _ ≤ c*(scoreScale*numer r e) := Nat.mul_le_mul_left _ (all_weights h e).2
    _ = _ := by simp only [Nat.mul_comm, Nat.mul_left_comm]

private theorem final_lower (c : ℕ) (rs : List ScoreRow) (es : List ℕ)
    (hg : rs.all rowGood = true) : c ≤ finalCost c rs es := by
  induction rs generalizing c es with
  | nil => exact le_rfl
  | cons r rs ih =>
    obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp hg
    cases es with
    | nil => exact (step_lower hr c 0).trans (ih _ _ hrest)
    | cons e es => exact (step_lower hr c e).trans (ih _ _ hrest)

private theorem combine_cost {f d' c' n' d c n : ℕ}
    (hr : f*d' ≤ c'*n') (hs : c'*d ≤ c*n) : f*(d*d') ≤ c*(n*n') := by
  calc
    _ = (f*d')*d := by ac_rfl
    _ ≤ (c'*n')*d := Nat.mul_le_mul_right _ hr
    _ = (c'*d)*n' := by ac_rfl
    _ ≤ (c*n)*n' := Nat.mul_le_mul_right _ hs
    _ = _ := Nat.mul_assoc _ _ _

def totalDen (rs : List ScoreRow) (es : List ℕ) := profileTau es ^ 37 * baseValue rs ^ 4
def totalNum (rs : List ScoreRow) (es : List ℕ) :=
  baseCount rs ^ 37 * profileValue (rs.map ScoreRow.prime) es ^ 4

/-- Multiplying the row inequalities bounds the accumulated rounded cost by the ratio of
the optimal score to the candidate score, where the score is the divisor count^37 / value^4. -/
private theorem final_upper (c : ℕ) (rs : List ScoreRow) (es : List ℕ) (hlen : es.length ≤ rs.length)
    (hg : rs.all rowGood = true) : finalCost c rs es * totalDen rs es ≤ c * totalNum rs es := by
  induction rs generalizing c es with
  | nil =>
    have hz : es = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst es
    simp [finalCost, totalDen, totalNum, baseCount, baseValue, profileTau, profileValue]
  | cons r rs ih =>
    obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp hg
    cases es with
    | nil =>
      have t := combine_cost (ih (costStep c r 0) [] (by simp) hrest) (step_upper hr c 0)
      simpa only [finalCost, totalDen, totalNum, baseCount, baseValue, profileTau, profileValue,
        denom, numer, List.map_cons, List.zipWith_cons_cons, List.prod_cons, List.map_nil,
        List.zipWith_nil_right, List.prod_nil, one_pow, zero_add, pow_zero, one_mul, mul_one,
        Nat.mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using t
    | cons e es =>
      have t := combine_cost (ih (costStep c r e) es (by simpa using hlen) hrest) (step_upper hr c e)
      simpa only [finalCost, totalDen, totalNum, baseCount, baseValue, profileTau, profileValue,
        denom, numer, List.map_cons, List.zipWith_cons_cons, List.prod_cons,
        Nat.mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using t

end HCN




namespace HCN

private theorem profile_positive {rs : List ScoreRow} (hg : rs.all rowGood = true) (es : List ℕ) :
    0 < profileValue (rs.map ScoreRow.prime) es := by
  induction rs generalizing es with
  | nil => simp [profileValue]
  | cons r rs ih =>
    cases es with
    | nil => simp [profileValue]
    | cons e es =>
      obtain ⟨hr,hrest⟩ := Bool.and_eq_true_iff.mp hg
      have hp : 0 < r.prime := (of_decide_eq_true (Bool.and_eq_true_iff.mp hr).1).1
      exact Nat.mul_pos (Nat.pow_pos hp) (ih hrest es)

private theorem search_sound {rs : List ScoreRow} (hg : rs.all rowGood = true)
    (es : List ℕ) (hl : es.length ≤ rs.length) (hp : ∀ e ∈ es, 0 < e)
    {c v d : ℕ} (hstart : scoreScale ≤ c) (hfin : finalCost c rs es ≤ scoreCap)
    (hsize : v * profileValue (rs.map ScoreRow.prime) es ≤ recordK)
    (checked : searchRows rs c v d = true) :
    recordOK (v*profileValue (rs.map ScoreRow.prime) es) (d*profileTau es) = true := by
  have hv : v ≤ recordK := (Nat.le_mul_of_pos_right _ (profile_positive hg es)).trans hsize
  have hc : c ≤ scoreCap := (final_lower c rs es hg).trans hfin
  have hneg : decide (scoreCap < c ∨ recordK < v) = false := decide_eq_false (by omega)
  induction rs generalizing es c v d with
  | nil =>
    have he : es = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst es
    simpa [searchRows, hneg, profileValue, profileTau] using checked
  | cons r rs ih =>
    simp only [searchRows, hneg, Bool.false_or] at checked
    obtain ⟨ hhere,hkids ⟩ := Bool.and_eq_true_iff.mp checked
    cases es with
    | nil => simpa [profileValue, profileTau] using hhere
    | cons e es =>
      obtain ⟨hr,hg'⟩ := Bool.and_eq_true_iff.mp hg
      have hnext : costStep c r e ≤ scoreCap :=
        (final_lower (costStep c r e) rs es hg').trans hfin
      have hepos := hp e (.head _)
      have helen : e < r.weights.length := by
        by_contra! he
        have hx : rowWeight r e = scoreCap+1 := by
          simp [rowWeight, List.getElem?_eq_none he]
        have hx' : rowWeight r e ≤ costStep c r e :=
          (Nat.le_div_iff_mul_le (by decide : 0 < scoreScale)).mpr
            (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hstart)
        omega
      have kk := List.all_eq_true.mp hkids (e-1) (List.mem_range.mpr (by omega))
      simp only [Nat.sub_add_cancel hepos, decide_eq_false (by omega : ¬ scoreCap < costStep c r e),
        Bool.false_or] at kk
      have hs' : (v*r.prime^e)*profileValue (rs.map ScoreRow.prime) es ≤ recordK := by
        simpa [profileValue,Nat.mul_assoc] using hsize
      have vv : v*r.prime^e ≤ recordK :=
        (Nat.le_mul_of_pos_right _ (profile_positive hg' es)).trans hs'
      have t := ih hg' es (by simpa using hl) (fun a h => hp a (.tail _ h))
        (hstart.trans (step_lower hr c e)) hfin hs' kk vv hnext
        (decide_eq_false (by omega))
      simpa [profileTau, profileValue, Nat.mul_assoc] using t

private theorem budget_bound {c cap S W V K n d D : ℕ}
    (upper : c*(d^37*V^4) ≤ S*(W^37*n^4))
    (lower : D ≤ d) (size : n ≤ K)
    (scale : S*W^37*K^4 < (cap+1)*D^37*V^4) : c ≤ cap := by
  have hp : c*(D^37*V^4) < (cap+1)*(D^37*V^4) := by
    calc
      _ ≤ c * (d^37*V^4) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left lower _))
      _ ≤ S*(W^37*n^4) := upper
      _ ≤ S*(W^37*K^4) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size _))
      _ < _ := by simpa only [Nat.mul_assoc] using scale
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right hp)

set_option maxRecDepth 4096 in
theorem compressed_record_bound {es : List ℕ} (hl : es.length ≤ scorePrimes.length)
    (hp : ∀ e ∈ es, 0 < e) (hsize : profileValue scorePrimes es ≤ recordK)
    (hcount : countH ≤ profileTau es)
    (bounds : scoreRows.all rowGood = true)
    (scale : scoreScale * baseCount scoreRows ^ 37 * recordK^4 <
        (scoreCap+1) * countH ^ 37 * baseValue scoreRows ^ 4)
    (checked : searchRows scoreRows scoreScale 1 1 = true) :
    recordH ≤ profileValue scorePrimes es ∧
      (countH < profileTau es → recordK ≤ profileValue scorePrimes es) := by
  have hu := final_upper scoreScale scoreRows es (by simpa [scorePrimes] using hl) bounds
  have hbudget : finalCost scoreScale scoreRows es ≤ scoreCap :=
    budget_bound (D := countH) (d := profileTau es) (V := baseValue scoreRows)
      (W := baseCount scoreRows) (n := profileValue scorePrimes es) (K := recordK)
      hu hcount hsize scale
  have res := search_sound bounds es (by simpa [scorePrimes] using hl) hp (le_refl scoreScale)
    hbudget (v := 1) (d := 1) (by simpa [scorePrimes] using hsize) checked
  simp only [one_mul] at res
  obtain ⟨h1,h2⟩ := of_decide_eq_true res
  exact ⟨h1 hcount,h2⟩

end HCN


namespace HCN
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem checkedBounds : scoreRows.all rowGood = true := by decide +kernel
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem checkedScale : scoreScale * baseCount scoreRows ^ 37 * recordK^4 <
    (scoreCap+1) * countH ^ 37 * baseValue scoreRows ^ 4 := by decide +kernel
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem checkedSearch : searchRows scoreRows scoreScale 1 1 = true := by decide +kernel

end HCN

namespace HCN

theorem recordProfile_bound {es : List ℕ} (hl : es.length ≤ scorePrimes.length)
    (hp : ∀ e ∈ es, 0 < e) (hsize : profileValue scorePrimes es ≤ recordK)
    (hcount : countH ≤ profileTau es) :
    recordH ≤ profileValue scorePrimes es ∧
      (countH < profileTau es → recordK ≤ profileValue scorePrimes es) :=
  compressed_record_bound hl hp hsize hcount checkedBounds checkedScale checkedSearch

end HCN

namespace HCN

private def factorValue : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p,e)::rest => p^e * factorValue rest

private def factorCount (f : List (ℕ × ℕ)) : ℕ := (f.map (fun pe => pe.2 + 1)).prod

private def verifiedFactors : List (ℕ × ℕ) → Bool
  | [] => true
  | (p,e)::rest => decide (p.Prime ∧ e ≠ 0 ∧ ¬p ∣ factorValue rest) && verifiedFactors rest

private theorem factors_sound {f : List (ℕ × ℕ)} (ok : verifiedFactors f = true) :
    factorValue f ≠ 0 ∧ tau (factorValue f) = factorCount f ∧
    (factorValue f).primeFactors.card = f.length := by
  induction f with
  | nil => simp [tau, factorValue, factorCount]
  | cons pe rest ih =>
    obtain ⟨p,e⟩ := pe
    obtain ⟨head, tailok⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨hp, he, hfresh⟩ : p.Prime ∧ e ≠ 0 ∧ ¬p ∣ factorValue rest := of_decide_eq_true head
    obtain ⟨hrest, hcount, hlength⟩ := ih tailok
    have hcop := (hp.coprime_iff_not_dvd.mpr hfresh).pow_left e
    have hpcount : (p^e).divisors.card = e + 1 := by
      rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    refine ⟨mul_ne_zero (pow_ne_zero _ hp.ne_zero) hrest, ?_, ?_⟩
    · change ((p^e)*(factorValue rest)).divisors.card = (e+1)*factorCount rest
      rw [hcop.card_divisors_mul, hpcount]
      exact congrArg ((e+1)* ·) hcount
    · have hmem : p ∉ (factorValue rest).primeFactors :=
        fun hm => hfresh (Nat.dvd_of_mem_primeFactors hm)
      rw [factorValue, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hrest,
        Nat.primeFactors_prime_pow he hp, Finset.singleton_union, Finset.card_insert_of_notMem hmem,
        hlength, List.length_cons]

private def factorsH : List (ℕ × ℕ) := [
  (2,10), (3,7), (5,5), (7,4), (11,3), (13,3), (17,2), (19,2), (23,2), (29,2),
  (31,2), (37,2), (41,1), (43,1), (47,1), (53,1), (59,1), (61,1), (67,1), (71,1),
  (73,1), (79,1), (83,1), (89,1), (97,1), (101,1), (103,1), (107,1), (109,1), (113,1),
  (127,1), (131,1), (137,1), (139,1), (149,1), (151,1), (157,1), (163,1), (167,1), (173,1),
  (179,1), (181,1), (191,1), (193,1), (197,1), (199,1), (211,1), (223,1), (227,1), (229,1),
  (233,1), (239,1), (241,1), (251,1), (257,1), (263,1), (269,1), (271,1), (277,1), (281,1),
  (283,1), (293,1), (307,1), (311,1), (313,1), (317,1), (331,1), (337,1), (347,1), (349,1),
  (353,1), (359,1), (367,1), (373,1), (379,1), (383,1), (389,1), (397,1), (401,1), (409,1),
  (419,1), (421,1), (431,1), (433,1), (439,1), (443,1), (449,1), (457,1), (461,1), (463,1),
  (467,1), (479,1), (487,1), (491,1), (499,1), (503,1), (509,1), (521,1), (523,1), (541,1),
  (547,1), (557,1), (563,1), (569,1), (571,1), (577,1), (587,1), (593,1), (599,1), (601,1),
  (607,1), (613,1), (617,1)]

theorem recordH_facts : tau recordH = countH ∧ recordH.primeFactors.card = 113 := by
  have ok : verifiedFactors factorsH = true := by decide +kernel
  have hval : factorValue factorsH = recordH := by decide +kernel
  have hτ : factorCount factorsH = countH := by decide +kernel
  have ⟨_,ht,hlen⟩ := factors_sound ok
  rw [hval] at ht hlen
  exact ⟨ht.trans hτ, hlen.trans (by decide +kernel)⟩

private def factorsK : List (ℕ × ℕ) := [
  (2,13), (3,8), (5,4), (7,4), (11,3), (13,3), (17,2), (19,2), (23,2), (29,2),
  (31,2), (37,2), (41,2), (43,2), (47,2), (53,1), (59,1), (61,1), (67,1), (71,1),
  (73,1), (79,1), (83,1), (89,1), (97,1), (101,1), (103,1), (107,1), (109,1), (113,1),
  (127,1), (131,1), (137,1), (139,1), (149,1), (151,1), (157,1), (163,1), (167,1), (173,1),
  (179,1), (181,1), (191,1), (193,1), (197,1), (199,1), (211,1), (223,1), (227,1), (229,1),
  (233,1), (239,1), (241,1), (251,1), (257,1), (263,1), (269,1), (271,1), (277,1), (281,1),
  (283,1), (293,1), (307,1), (311,1), (313,1), (317,1), (331,1), (337,1), (347,1), (349,1),
  (353,1), (359,1), (367,1), (373,1), (379,1), (383,1), (389,1), (397,1), (401,1), (409,1),
  (419,1), (421,1), (431,1), (433,1), (439,1), (443,1), (449,1), (457,1), (461,1), (463,1),
  (467,1), (479,1), (487,1), (491,1), (499,1), (503,1), (509,1), (521,1), (523,1), (541,1),
  (547,1), (557,1), (563,1), (569,1), (571,1), (577,1), (587,1), (593,1), (599,1), (601,1),
  (607,1)]

theorem recordK_facts : tau recordK = countK ∧ recordK.primeFactors.card = 111 := by
  have ok : verifiedFactors factorsK = true := by decide +kernel
  have hval : factorValue factorsK = recordK := by decide +kernel
  have hτ : factorCount factorsK = countK := by decide +kernel
  have ⟨_,ht,hlen⟩ := factors_sound ok
  rw [hval] at ht hlen
  exact ⟨ht.trans hτ, hlen.trans (by decide +kernel)⟩

theorem endpoint_prime_facts :
    613 ∣ recordH ∧ 617 ∣ recordH ∧ ¬613 ∣ recordK ∧ ¬617 ∣ recordK := by decide +kernel

end HCN

namespace HCN

private def noSkippedPrimes (lo : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => decide (∀ q ∈ Finset.Ico lo p, ¬ Nat.Prime q) && noSkippedPrimes (p+1) ps

private lemma support_head {lo p q : ℕ} {ps : List ℕ}
    (h : noSkippedPrimes lo (p::ps) = true) (hq : q.Prime) (hl : lo ≤ q) : p ≤ q := by
  by_contra! hbad
  have hs : (∀ i ∈ Finset.Ico lo p, ¬ Nat.Prime i) ∧ noSkippedPrimes (p+1) ps = true := by simpa [noSkippedPrimes] using h
  have hgap : ∀ i ∈ Finset.Ico lo p, ¬ Nat.Prime i := hs.1
  exact hgap q (Finset.mem_Ico.mpr ⟨hl,hbad⟩) hq

private lemma power_prod_pos (f : ℕ → ℕ) {qs : List ℕ} (h : ∀ q ∈ qs, q.Prime) :
    0 < (qs.map (fun q => q^f q)).prod := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    exact Nat.mul_pos (pow_pos (h q (by simp)).pos _)
      (ih (fun j hj => h j (by simp [hj])))

private lemma compress_values (f : ℕ → ℕ) {ps qs : List ℕ} {lo : ℕ}
    (init : noSkippedPrimes lo ps = true) (sorted : qs.Pairwise (· < ·))
    (data : ∀ q ∈ qs, lo ≤ q ∧ Nat.Prime q) :
    profileValue ps (qs.map f) ≤ (qs.map (fun q => q^f q)).prod := by
  induction ps generalizing qs lo with
  | nil => exact power_prod_pos f (fun j hj => (data j hj).2)
  | cons p ps ih =>
    cases qs with
    | nil => simp [profileValue]
    | cons q qs =>
      have ⟨hlo,hp⟩ := data q (by simp)
      have hhead := support_head init hp hlo
      have hs := List.pairwise_cons.mp sorted
      have ht : noSkippedPrimes (p+1) ps = true := by
        have hx : (∀ i ∈ Finset.Ico lo p, ¬ Nat.Prime i) ∧ noSkippedPrimes (p+1) ps = true := by simpa [noSkippedPrimes] using init
        exact hx.2
      have rest := ih ht hs.2
        (fun j hj => ⟨by have := hs.1 j hj; omega, (data j (by simp [hj])).2⟩)
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hhead _) rest

private lemma compressed_primorial (f : ℕ → ℕ) {ps qs : List ℕ} {lo : ℕ}
    (init : noSkippedPrimes lo ps = true) (sorted : qs.Pairwise (· < ·))
    (data : ∀ q ∈ qs, lo ≤ q ∧ Nat.Prime q ∧ 0 < f q)
    (hlen : ps.length ≤ qs.length) :
    ps.prod ≤ (qs.map (fun q => q^f q)).prod := by
  induction ps generalizing qs lo with
  | nil => exact power_prod_pos f (fun j hj => (data j hj).2.1)
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      have ⟨hlo,hp,he⟩ := data q (by simp)
      have hhead := support_head init hp hlo
      have hs := List.pairwise_cons.mp sorted
      have ht : noSkippedPrimes (p+1) ps = true := by
        have hx : (∀ i ∈ Finset.Ico lo p, ¬ Nat.Prime i) ∧ noSkippedPrimes (p+1) ps = true := by simpa [noSkippedPrimes] using init
        exact hx.2
      have rest := ih ht hs.2
        (fun j hj => ⟨by have := hs.1 j hj; omega, (data j (by simp [hj])).2⟩)
        (by simpa using hlen)
      have hpow : q ≤ q^(f q) := Nat.le_self_pow (by omega : f q ≠ 0) q
      exact Nat.mul_le_mul (hhead.trans hpow) rest

private lemma prod_over_sort (s : Finset ℕ) (f : ℕ → ℕ) :
    (s.sort.map f).prod = ∏ q ∈ s, f q := by
  change (Multiset.map f (s.sort : Multiset ℕ)).prod = _
  rw [Finset.sort_eq]
  rfl

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
lemma compression_certificate (z : ℕ) (hz : 0 < z) (hk : z ≤ recordK) :
    ∃ es : List ℕ, es.length ≤ scorePrimes.length ∧ (∀ e ∈ es, 0 < e) ∧
      profileValue scorePrimes es ≤ z ∧ profileTau es = tau z := by
  let qs : List ℕ := z.primeFactors.sort
  let f : ℕ → ℕ := z.factorization
  have hs : qs.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp z.primeFactors.sortedLT_sort
  have valid (q : ℕ) (hq : q ∈ qs) : 0 ≤ q ∧ q.Prime ∧ 0 < f q := by
    have cm : q ∈ z.primeFactors := (Finset.mem_sort (· ≤ ·)).mp hq
    exact ⟨Nat.zero_le _, Nat.prime_of_mem_primeFactors cm, Finsupp.mem_support_iff.mp cm |> Nat.pos_of_ne_zero⟩
  have hv : (qs.map (fun q => q^f q)).prod = z :=
    (prod_over_sort _ _).trans (Nat.prod_primeFactors_pow_factorization hz.ne').symm
  have init : noSkippedPrimes 0 (scorePrimes ++ [673]) = true := by decide +kernel
  have init' : noSkippedPrimes 0 scorePrimes = true := by decide +kernel
  have hlen : qs.length ≤ scorePrimes.length := by
    by_contra! hl
    have big := compressed_primorial f init hs valid
      (show (scorePrimes ++ [673]).length ≤ qs.length by simp; omega)
    rw [hv] at big
    have limit : recordK < (scorePrimes++[673]).prod := by decide +kernel
    omega
  refine ⟨qs.map f, by simpa, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
    exact (valid q hq).2.2
  · exact (compress_values f init' hs (fun q hq => ⟨Nat.zero_le _, (valid q hq).2.1⟩)).trans_eq hv
  · change ((qs.map f).map (·+1)).prod = z.divisors.card
    rw [List.map_map, prod_over_sort]
    have he := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
       (k := 0) hz.ne'
    simpa [ArithmeticFunction.sigma_apply, Function.comp_def, f] using he.symm

end HCN

namespace HCN

theorem pair_consecutive_of_compression
    (compress : ∀ z : ℕ, 0 < z → z ≤ recordK →
      ∃ es : List ℕ, es.length ≤ scorePrimes.length ∧ (∀ e ∈ es, 0 < e) ∧
        profileValue scorePrimes es ≤ z ∧ profileTau es = tau z) :
    Consecutive recordH recordK := by
  have hcount := recordH_facts.1
  have kcount := recordK_facts.1
  have hlt : recordH < recordK := by decide
  have hD : countH < countK := by decide
  have hp : 0 < recordH := by decide
  have hbound {z : ℕ} (hz : 0 < z) (hk : z ≤ recordK) (hd : countH ≤ tau z) :
      recordH ≤ z ∧ (countH < tau z → recordK ≤ z) := by
    obtain ⟨es,hel,hepos,hv,ht⟩ := compress _ hz hk
    obtain ⟨hh,hk'⟩ := recordProfile_bound hel hepos (hv.trans hk) (by simpa only [ht] using hd)
    exact ⟨hh.trans hv, fun h => (hk' (by simpa only [ht] using h)).trans hv⟩
  refine ⟨⟨hp, ?_⟩, ⟨hp.trans hlt, ?_⟩, hlt, ?_⟩
  · intro z hz hzh
    rw [hcount]
    by_contra! h
    exact (Nat.not_le_of_lt hzh) (hbound hz (hzh.trans hlt).le h).1
  · intro z hz hzk
    rw [kcount]
    by_contra! h
    have hd := hD.trans_le h
    exact (Nat.not_le_of_lt hzk) ((hbound hz hzk.le hd.le).2 hd)
  · intro z hhz hzk hrec
    have h := hrec.2 _ hp hhz
    rw [hcount] at h
    exact (Nat.not_le_of_lt hzk) ((hbound (hp.trans hhz) hzk.le h.le).2 h)

end HCN

namespace HCN

def BoxGap (h k : ℕ) : Prop := ∀ z : ℕ, InBox h k z → z ≤ k → z ≠ k → z ≤ h

private theorem reach_state {h k t x : ℕ} (r : Reach h k t x) :
    0 < x ∧ InBox h k x ∧ x ≤ k := by
  cases r with
  | start pos ceiling floor => exact ⟨pos, ⟨Nat.gcd_dvd_left .., Nat.dvd_lcm_left ..⟩, ceiling⟩
  | step prev move pos box ceiling floor => exact ⟨pos, box, ceiling⟩

private theorem tau_mul_fresh {p y : ℕ} (hp : p.Prime) (fresh : ¬p ∣ y) :
    tau (p * y) = 2 * tau y := by
  rw [tau, (hp.coprime_iff_not_dvd.mpr fresh).card_divisors_mul, hp.divisors]
  simp [tau, Ne.symm hp.ne_one]

private theorem last_deletion {a b p h k y : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hp : p.Prime) (hab : a ≠ b)
    (ah : a ∣ h) (bh : b ∣ h) (ak : ¬a ∣ k) (bk : ¬b ∣ k)
    (s : a ∣ p*y ∨ b ∣ p*y) (ay : ¬a ∣ y) (byy : ¬b ∣ y) :
    (¬p ∣ y) ∧ p*y ≠ h ∧ p*y ≠ k := by
  have aa : ∀ (_ : a ∣ p*y), a = p := fun hh =>
    (Nat.prime_dvd_prime_iff_eq ha hp).mp ((ha.dvd_mul.mp hh).resolve_right ay)
  have bb : ∀ (_ : b ∣ p*y), b = p := fun hh =>
    (Nat.prime_dvd_prime_iff_eq hb hp).mp ((hb.dvd_mul.mp hh).resolve_right byy)
  refine ⟨s.elim (fun hh => aa hh ▸ ay) (fun hh => bb hh ▸ byy), ?_, ?_⟩
  · rintro heq
    exact hab ((aa (heq ▸ ah)).trans (bb (heq ▸ bh)).symm)
  · rintro heq
    exact s.elim (fun hh => ak (heq ▸ hh)) (fun hh => bk (heq ▸ hh))

/-- At a floor of at least half the initial divisor count, one of the two source
primes must survive every move. The deletion that removes the last survivor would
halve the divisor count of a state strictly smaller than the source. -/
theorem retained_prime {h k a b t x : ℕ} (hh : IsRecord h) (gap : BoxGap h k)
    (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ah : a ∣ h) (bh : b ∣ h) (ak : ¬a ∣ k) (bk : ¬b ∣ k)
    (half : tau h ≤ 2*t) (r : Reach h k t x) : a ∣ x ∨ b ∣ x := by
  induction r with
  | start => exact Or.inl ah
  | @step x y prev move pos box ceiling floor ih =>
    by_contra! hbad
    obtain ⟨ay, byy⟩ := hbad
    obtain ⟨p, hp, ⟨hins, _⟩ | ⟨hdel, _⟩⟩ := move
    · rw [hins] at ay byy
      exact ih.elim (fun hax => ay (dvd_mul_of_dvd_right hax p))
        (fun hbx => byy (dvd_mul_of_dvd_right hbx p))
    · obtain ⟨xpos, xbox, xceil⟩ := reach_state prev
      subst x
      obtain ⟨fresh, ne_h, ne_k⟩ :=
        last_deletion ha hb hp hab ah bh ak bk ih ay byy
      have hlt := hh.2 (p*y) xpos (lt_of_le_of_ne (gap _ xbox xceil ne_k) ne_h)
      rw [tau_mul_fresh hp fresh] at hlt
      omega

theorem two_lost_primes {h k a b : ℕ} (hh : IsRecord h) (gap : BoxGap h k)
    (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ah : a ∣ h) (bh : b ∣ h) (ak : ¬a ∣ k) (bk : ¬b ∣ k) :
    capacity h k < 1 / 2 := by
  classical
  have tau_pos : 0 < tau h :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hh.1.ne'⟩
  have hlt : 2 * bottleneck h k < tau h := by
    by_contra! hf
    have hn : bottleneck h k ≠ 0 := by omega
    have reach : Reach h k (bottleneck h k) k := Nat.findGreatest_of_ne_zero (P := fun t => Reach h k t k) (n := tau h) rfl hn
    exact (retained_prime hh gap ha hb hab ah bh ak bk hf reach).elim ak bk
  have hrat : (2:ℚ) * bottleneck h k < tau h := by exact_mod_cast hlt
  have hpos : (0:ℚ) < tau h := by exact_mod_cast tau_pos
  rw [capacity, div_lt_div_iff₀ hpos (by norm_num)]
  linarith

end HCN

namespace HCN

private lemma tau_over {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hd : n ∣ m) :
    tau n = ∏ p ∈ m.primeFactors, (n.factorization p + 1) := by
  rw [tau, Nat.card_divisors hn]
  apply Finset.prod_subset (Nat.primeFactors_mono hd hm)
  intro p _ hpn
  have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
  simp [hz]

private lemma inside_products {a b c d : ℕ} (hl : min a b ≤ c) (hu : c ≤ max a b)
    (he : a + b = c + d) : (a+1)*(b+1) ≤ (c+1)*(d+1) := by
  have aux {i j : ℕ} (hij : i ≤ j) (hic : i ≤ c) (hcj : c ≤ j)
      (heq : i+j=c+d) : (i+1)*(j+1) ≤ (c+1)*(d+1) := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hic
    have hid : i ≤ d := by omega
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hid
    have hj : j = i+u+v := by omega
    rw [hu,hv,hj]
    nlinarith
  rcases le_total a b with hab | hba
  · exact aux hab (by simpa [min_eq_left hab] using hl)
      (by simpa [max_eq_right hab] using hu) he
  · rw [mul_comm]
    exact aux hba (by simpa [min_eq_right hba] using hl)
      (by simpa [max_eq_left hba] using hu) (by omega)

theorem divisor_reflection {h k z w : ℕ} (hh : h ≠ 0) (hk : k ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) (box : InBox h k z) (eqw : h*k=z*w) :
    tau h * tau k ≤ tau z * tau w := by
  have hprod := mul_ne_zero hh hk
  have hzdiv : z ∣ h*k := by rw [eqw]; exact dvd_mul_right .. 
  have hwdiv : w ∣ h*k := by rw [eqw]; exact dvd_mul_left ..
  rw [tau_over hh hprod (dvd_mul_right h k), tau_over hk hprod (dvd_mul_left k h),
    tau_over hz hprod hzdiv, tau_over hw hprod hwdiv, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (by intros; omega)
  intro p _
  have hgc : h.gcd k ≠ 0 := by simp [Nat.gcd_eq_zero_iff, hh]
  have hlow := (Nat.factorization_le_iff_dvd hgc hz).mpr box.1 p
  have hupp := (Nat.factorization_le_iff_dvd hz (Nat.lcm_ne_zero hh hk)).mpr box.2 p
  rw [Nat.factorization_gcd hh hk] at hlow
  rw [Nat.factorization_lcm hh hk] at hupp
  apply inside_products hlow hupp
  have facteq := congrArg (fun n : ℕ => n.factorization p) eqw
  simpa [Nat.factorization_mul hh hk, Nat.factorization_mul hz hw] using facteq

theorem before_next_record {h k z : ℕ} (hc : Consecutive h k) (hz : 0<z)
    (hlt : z<k) : tau z ≤ tau h := by
  classical
  by_contra! hbad
  have large : ∀ m, 0 < m → tau h < tau m → h < m := by
    intro m hm hmτ
    rcases lt_trichotomy m h with hmh | he | hhm
    · have := hc.1.2 m hm hmh
      omega
    · subst m; omega
    · exact hhm
  have ex : ∃ m : ℕ, 0 < m ∧ tau h < tau m := ⟨z,hz,hbad⟩
  let m := Nat.find ex
  have hm : 0 < m ∧ tau h < tau m := Nat.find_spec ex
  have hmk : m < k := lt_of_le_of_lt (Nat.find_min' ex ⟨hz,hbad⟩) hlt
  apply hc.2.2.2 m (large m hm.1 hm.2) hmk
  refine ⟨hm.1, ?_⟩
  intro j hj hjm
  have hlo : tau j ≤ tau h := by
    by_contra! hj'
    exact Nat.find_min ex hjm ⟨hj,hj'⟩
  omega

/-- Theorem 4.2 of the source follows by reflecting a putative interior state. -/
theorem consecutive_box_gap {h k : ℕ} (hc : Consecutive h k) : BoxGap h k := by
  intro z box zle zne
  by_contra! hz
  have zlt := lt_of_le_of_ne zle zne
  obtain ⟨w, eqw⟩ := box.2.trans (Nat.lcm_dvd_mul h k)
  have hh := hc.1.1
  have hk := hc.2.1.1
  have zp := hh.trans hz
  have below : z*h < z*w := by
    rw [← eqw, mul_comm z h]
    exact Nat.mul_lt_mul_of_pos_left zlt hh
  have above : z*w < z*k := by
    rw [← eqw]
    exact Nat.mul_lt_mul_of_pos_right hz hk
  have hlt : h < w := Nat.lt_of_mul_lt_mul_left below
  have kgt : w < k := Nat.lt_of_mul_lt_mul_left above
  have wp := hh.trans hlt
  have hzτ := before_next_record hc zp zlt
  have hwτ := before_next_record hc wp kgt
  have prod := divisor_reflection hh.ne' hk.ne' zp.ne' wp.ne' box eqw
  have strict := hc.2.1.2 h hh hc.2.2.1
  have τpos : 0<tau h := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hh.ne'⟩
  exact (Nat.not_lt_of_ge ((Nat.mul_le_mul hzτ hwτ).trans' prod))
    (Nat.mul_lt_mul_of_pos_left strict τpos)

end HCN

namespace HCN

/-- The same record transition refutes both universal statements in Section 9. -/
theorem refutes_both (hc : Consecutive recordH recordK) :
    (¬∀ h k : ℕ, Consecutive h k → 1 / 2 ≤ capacity h k) ∧
    (¬∀ h k : ℕ, Consecutive h k →
      (capacity h k = 1 / 2 ↔ k.primeFactors.card < h.primeFactors.card)) := by
  obtain ⟨hu,hv,ku,kv⟩ := endpoint_prime_facts
  have hcap := two_lost_primes hc.1 (consecutive_box_gap hc)
    (by decide +kernel : Nat.Prime 613) (by decide +kernel : Nat.Prime 617)
    (by decide : 613 ≠ 617) hu hv ku kv
  have shrink : recordK.primeFactors.card < recordH.primeFactors.card := by
    rw [recordK_facts.2, recordH_facts.2]
    decide
  exact ⟨fun h => hcap.not_ge (h _ _ hc),
    fun h => hcap.ne ((h _ _ hc).mpr shrink)⟩

end HCN

theorem HCN.counterexample_consecutive : HCN.Consecutive HCN.recordH HCN.recordK :=
  HCN.pair_consecutive_of_compression HCN.compression_certificate

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2608_17045.main) := by
  intro h
  exact (HCN.refutes_both HCN.counterexample_consecutive).1 h.1
