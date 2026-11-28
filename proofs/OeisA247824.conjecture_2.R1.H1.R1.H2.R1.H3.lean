import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals

open ArithmeticFunction Finset

namespace Astra247824.Ordinary

/-- The same trial divisors as Mathlib's minFacAux, with structural fuel so
the kernel can reduce the finite computation without unfolding accessibility. -/
private def trialAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => Nat.minFacAux n k
  | fuel+1, k => if n < k*k then n else if k ∣ n then k else trialAux n fuel (k+2)

private theorem trialAux_eq (n fuel k : ℕ) : trialAux n fuel k = Nat.minFacAux n k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [trialAux, Nat.minFacAux]
    split <;> try rfl
    split <;> try rfl
    exact ih _

private def least (n : ℕ) : ℕ := if 2 ∣ n then 2 else trialAux n 105 3

private theorem least_eq (n : ℕ) : least n = n.minFac := by
  simp only [least, trialAux_eq, Nat.minFac]

/-- Strip a prime factor and detect repeated factors. Sixteen steps suffice
for the concrete range. The fallback makes the equivalence true for every input. -/
noncomputable def mu : ℕ → ℕ → ℤ
  | 0, d => moebius d
  | fuel+1, d =>
      if d = 0 then 0 else if d = 1 then 1 else
      let p := least d
      let q := d/p
      if p ∣ q then 0 else -mu fuel q

theorem mu_eq (fuel d : ℕ) : mu fuel d = moebius d := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    by_cases hz : d=0
    · subst d; simp [mu]
    by_cases ho : d=1
    · subst d; simp [mu]
    rw [mu, if_neg hz, if_neg ho, least_eq]
    let p := d.minFac
    let q := d / p
    have hp : p.Prime := Nat.minFac_prime ho
    have prod : q*p = d := Nat.div_mul_cancel (Nat.minFac_dvd d)
    change (if p ∣ q then 0 else -mu fuel q) = moebius d
    split
    next hd =>
      apply Eq.symm
      apply moebius_eq_zero_of_not_squarefree
      intro sf
      apply Nat.squarefree_iff_prime_squarefree.mp sf p hp
      exact prod ▸ Nat.mul_dvd_mul hd (dvd_refl p)
    next hd =>
      rw [ih, ← prod, isMultiplicative_moebius.map_mul_of_coprime
        (hp.coprime_iff_not_dvd.mpr hd).symm, moebius_apply_prime hp, mul_neg_one]

private def treeSum (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, lo => f lo
  | k+1, lo => treeSum f k lo + treeSum f k (lo+2^k)

private theorem treeSum_eq (f : ℕ → ℤ) (k lo : ℕ) :
    treeSum f k lo = ∑ d ∈ Ico lo (lo+2^k), f d := by
  induction k generalizing lo with
  | zero => simp [treeSum]
  | succ k ih =>
    rw [treeSum, ih, ih, Finset.sum_Ico_consecutive f (Nat.le_add_right lo _) (Nat.le_add_right (lo+2^k) _)]
    congr 2
    rw [pow_succ]
    omega

noncomputable def term (d : ℕ) : ℤ :=
  if d ≤ 43399 then mu 16 d * ((81744924555066 / d : ℕ) : ℤ) else 0

theorem sum_eq : treeSum term 16 0 =
    ∑ d ∈ (Icc 1 43399).filter Squarefree, moebius d * ((81744924555066 / d : ℕ) : ℤ) := by
  rw [treeSum_eq]
  let s := (Icc 1 43399).filter Squarefree
  have incl : s ⊆ Ico 0 (0+2^16) := by
    intro d hd
    have ⟨_, h⟩ := mem_Icc.mp (mem_filter.mp hd).1
    exact mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩
  calc
    _ = ∑ d ∈ s, term d := (Finset.sum_subset incl (by
      intro d _ h
      by_cases high : d ≤ 43399
      · by_cases zero : d=0
        · subst d; simp [term, mu_eq]
        · have ns : ¬Squarefree d := fun sf => h (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,high⟩,sf⟩)
          simp [term, high, mu_eq, moebius_eq_zero_of_not_squarefree ns]
      · simp [term, high])).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have high := (mem_Icc.mp (mem_filter.mp hd).1).2
      simp [term, high, mu_eq]

private theorem join {f : ℕ → ℤ} {k lo : ℕ} {a b : ℤ}
    (left : treeSum f k lo = a) (right : treeSum f k (lo+2^k) = b) :
    treeSum f (k+1) lo = a+b := congrArg₂ (·+·) left right


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_0 : treeSum term 9 0 = (-373074018027 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_1 : treeSum term 9 512 = (250867530058 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_2 : treeSum term 9 1024 = (206640348501 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_3 : treeSum term 9 1536 = (264976157829 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_4 : treeSum term 9 2048 = (-439866822364 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_5 : treeSum term 9 2560 = (35130446963 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_6 : treeSum term 9 3072 = (190718259648 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_7 : treeSum term 9 3584 = (-471936304042 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_8 : treeSum term 9 4096 = (358069588389 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_9 : treeSum term 9 4608 = (-7327002897 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_10 : treeSum term 9 5120 = (225359136461 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_11 : treeSum term 9 5632 = (-280725122210 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_12 : treeSum term 9 6144 = (-106712494327 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_13 : treeSum term 9 6656 = (133910803148 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_14 : treeSum term 9 7168 = (59589221429 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_15 : treeSum term 9 7680 = (189355928823 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_16 : treeSum term 9 8192 = (-55846691096 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_17 : treeSum term 9 8704 = (-164828509380 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_18 : treeSum term 9 9216 = (-265734042461 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_19 : treeSum term 9 9728 = (137980534873 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_20 : treeSum term 9 10240 = (-25746087354 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_21 : treeSum term 9 10752 = (127699608388 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_22 : treeSum term 9 11264 = (310178542750 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_23 : treeSum term 9 11776 = (-145403473203 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_24 : treeSum term 9 12288 = (-47659334499 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_25 : treeSum term 9 12800 = (-183154963489 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_26 : treeSum term 9 13312 = (97846397418 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_27 : treeSum term 9 13824 = (59260304446 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_28 : treeSum term 9 14336 = (-144189871709 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_29 : treeSum term 9 14848 = (33833805629 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_30 : treeSum term 9 15360 = (-68444520602 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_31 : treeSum term 9 15872 = (-51225392750 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_32 : treeSum term 9 16384 = (83559231051 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_33 : treeSum term 9 16896 = (8719216991 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_34 : treeSum term 9 17408 = (45993255742 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_35 : treeSum term 9 17920 = (-72516127414 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_36 : treeSum term 9 18432 = (213210593296 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_37 : treeSum term 9 18944 = (51799652061 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_38 : treeSum term 9 19456 = (-24933782642 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_39 : treeSum term 9 19968 = (-53098373248 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_40 : treeSum term 9 20480 = (52060190471 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_41 : treeSum term 9 20992 = (-61213364281 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_42 : treeSum term 9 21504 = (-75755045515 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_43 : treeSum term 9 22016 = (-81437908809 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_44 : treeSum term 9 22528 = (-17708749138 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_45 : treeSum term 9 23040 = (-17719280466 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_46 : treeSum term 9 23552 = (-68453940845 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_47 : treeSum term 9 24064 = (-3803738276 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_48 : treeSum term 9 24576 = (125371234566 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_49 : treeSum term 9 25088 = (16629289000 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_50 : treeSum term 9 25600 = (47092195129 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_51 : treeSum term 9 26112 = (21484087665 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_52 : treeSum term 9 26624 = (-88543825943 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_53 : treeSum term 9 27136 = (107393624833 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_54 : treeSum term 9 27648 = (-50022131674 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_55 : treeSum term 9 28160 = (-34188533505 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_56 : treeSum term 9 28672 = (5235616353 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_57 : treeSum term 9 29184 = (77500269581 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_58 : treeSum term 9 29696 = (-40593700575 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_59 : treeSum term 9 30208 = (61864945907 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_60 : treeSum term 9 30720 = (18973396213 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_61 : treeSum term 9 31232 = (20966485246 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_62 : treeSum term 9 31744 = (25943376508 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_63 : treeSum term 9 32256 = (-68044342422 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_64 : treeSum term 9 32768 = (-39801151914 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_65 : treeSum term 9 33280 = (-80495491190 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_66 : treeSum term 9 33792 = (-9562117668 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_67 : treeSum term 9 34304 = (-7121575831 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_68 : treeSum term 9 34816 = (5015137566 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_69 : treeSum term 9 35328 = (36702437763 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_70 : treeSum term 9 35840 = (18150351699 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_71 : treeSum term 9 36352 = (-6606571022 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_72 : treeSum term 9 36864 = (-54981516547 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_73 : treeSum term 9 37376 = (-6545568117 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_74 : treeSum term 9 37888 = (-10508076836 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_75 : treeSum term 9 38400 = (44672843516 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_76 : treeSum term 9 38912 = (-8086354257 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_77 : treeSum term 9 39424 = (24805946922 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_78 : treeSum term 9 39936 = (10117689593 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_79 : treeSum term 9 40448 = (66850635 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_80 : treeSum term 9 40960 = (-5931376463 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_81 : treeSum term 9 41472 = (-56733253482 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_82 : treeSum term 9 41984 = (-44472781194 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_83 : treeSum term 9 42496 = (-28814634793 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_84 : treeSum term 9 43008 = (66236057595 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_85 : treeSum term 9 43520 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_86 : treeSum term 9 44032 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_87 : treeSum term 9 44544 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_88 : treeSum term 9 45056 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_89 : treeSum term 9 45568 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_90 : treeSum term 9 46080 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_91 : treeSum term 9 46592 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_92 : treeSum term 9 47104 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_93 : treeSum term 9 47616 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_94 : treeSum term 9 48128 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_95 : treeSum term 9 48640 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_96 : treeSum term 9 49152 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_97 : treeSum term 9 49664 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_98 : treeSum term 9 50176 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_99 : treeSum term 9 50688 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_100 : treeSum term 9 51200 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_101 : treeSum term 9 51712 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_102 : treeSum term 9 52224 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_103 : treeSum term 9 52736 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_104 : treeSum term 9 53248 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_105 : treeSum term 9 53760 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_106 : treeSum term 9 54272 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_107 : treeSum term 9 54784 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_108 : treeSum term 9 55296 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_109 : treeSum term 9 55808 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_110 : treeSum term 9 56320 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_111 : treeSum term 9 56832 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_112 : treeSum term 9 57344 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_113 : treeSum term 9 57856 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_114 : treeSum term 9 58368 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_115 : treeSum term 9 58880 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_116 : treeSum term 9 59392 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_117 : treeSum term 9 59904 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_118 : treeSum term 9 60416 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_119 : treeSum term 9 60928 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_120 : treeSum term 9 61440 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_121 : treeSum term 9 61952 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_122 : treeSum term 9 62464 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_123 : treeSum term 9 62976 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_124 : treeSum term 9 63488 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_125 : treeSum term 9 64000 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_126 : treeSum term 9 64512 = (0 : ℤ) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem chunk9_127 : treeSum term 9 65024 = (0 : ℤ) := by decide +kernel
private theorem chunk10_0 : treeSum term 10 0 = (-122206487969 : ℤ) := join chunk9_0 chunk9_1
private theorem chunk10_1 : treeSum term 10 1024 = (471616506330 : ℤ) := join chunk9_2 chunk9_3
private theorem chunk10_2 : treeSum term 10 2048 = (-404736375401 : ℤ) := join chunk9_4 chunk9_5
private theorem chunk10_3 : treeSum term 10 3072 = (-281218044394 : ℤ) := join chunk9_6 chunk9_7
private theorem chunk10_4 : treeSum term 10 4096 = (350742585492 : ℤ) := join chunk9_8 chunk9_9
private theorem chunk10_5 : treeSum term 10 5120 = (-55365985749 : ℤ) := join chunk9_10 chunk9_11
private theorem chunk10_6 : treeSum term 10 6144 = (27198308821 : ℤ) := join chunk9_12 chunk9_13
private theorem chunk10_7 : treeSum term 10 7168 = (248945150252 : ℤ) := join chunk9_14 chunk9_15
private theorem chunk10_8 : treeSum term 10 8192 = (-220675200476 : ℤ) := join chunk9_16 chunk9_17
private theorem chunk10_9 : treeSum term 10 9216 = (-127753507588 : ℤ) := join chunk9_18 chunk9_19
private theorem chunk10_10 : treeSum term 10 10240 = (101953521034 : ℤ) := join chunk9_20 chunk9_21
private theorem chunk10_11 : treeSum term 10 11264 = (164775069547 : ℤ) := join chunk9_22 chunk9_23
private theorem chunk10_12 : treeSum term 10 12288 = (-230814297988 : ℤ) := join chunk9_24 chunk9_25
private theorem chunk10_13 : treeSum term 10 13312 = (157106701864 : ℤ) := join chunk9_26 chunk9_27
private theorem chunk10_14 : treeSum term 10 14336 = (-110356066080 : ℤ) := join chunk9_28 chunk9_29
private theorem chunk10_15 : treeSum term 10 15360 = (-119669913352 : ℤ) := join chunk9_30 chunk9_31
private theorem chunk10_16 : treeSum term 10 16384 = (92278448042 : ℤ) := join chunk9_32 chunk9_33
private theorem chunk10_17 : treeSum term 10 17408 = (-26522871672 : ℤ) := join chunk9_34 chunk9_35
private theorem chunk10_18 : treeSum term 10 18432 = (265010245357 : ℤ) := join chunk9_36 chunk9_37
private theorem chunk10_19 : treeSum term 10 19456 = (-78032155890 : ℤ) := join chunk9_38 chunk9_39
private theorem chunk10_20 : treeSum term 10 20480 = (-9153173810 : ℤ) := join chunk9_40 chunk9_41
private theorem chunk10_21 : treeSum term 10 21504 = (-157192954324 : ℤ) := join chunk9_42 chunk9_43
private theorem chunk10_22 : treeSum term 10 22528 = (-35428029604 : ℤ) := join chunk9_44 chunk9_45
private theorem chunk10_23 : treeSum term 10 23552 = (-72257679121 : ℤ) := join chunk9_46 chunk9_47
private theorem chunk10_24 : treeSum term 10 24576 = (142000523566 : ℤ) := join chunk9_48 chunk9_49
private theorem chunk10_25 : treeSum term 10 25600 = (68576282794 : ℤ) := join chunk9_50 chunk9_51
private theorem chunk10_26 : treeSum term 10 26624 = (18849798890 : ℤ) := join chunk9_52 chunk9_53
private theorem chunk10_27 : treeSum term 10 27648 = (-84210665179 : ℤ) := join chunk9_54 chunk9_55
private theorem chunk10_28 : treeSum term 10 28672 = (82735885934 : ℤ) := join chunk9_56 chunk9_57
private theorem chunk10_29 : treeSum term 10 29696 = (21271245332 : ℤ) := join chunk9_58 chunk9_59
private theorem chunk10_30 : treeSum term 10 30720 = (39939881459 : ℤ) := join chunk9_60 chunk9_61
private theorem chunk10_31 : treeSum term 10 31744 = (-42100965914 : ℤ) := join chunk9_62 chunk9_63
private theorem chunk10_32 : treeSum term 10 32768 = (-120296643104 : ℤ) := join chunk9_64 chunk9_65
private theorem chunk10_33 : treeSum term 10 33792 = (-16683693499 : ℤ) := join chunk9_66 chunk9_67
private theorem chunk10_34 : treeSum term 10 34816 = (41717575329 : ℤ) := join chunk9_68 chunk9_69
private theorem chunk10_35 : treeSum term 10 35840 = (11543780677 : ℤ) := join chunk9_70 chunk9_71
private theorem chunk10_36 : treeSum term 10 36864 = (-61527084664 : ℤ) := join chunk9_72 chunk9_73
private theorem chunk10_37 : treeSum term 10 37888 = (34164766680 : ℤ) := join chunk9_74 chunk9_75
private theorem chunk10_38 : treeSum term 10 38912 = (16719592665 : ℤ) := join chunk9_76 chunk9_77
private theorem chunk10_39 : treeSum term 10 39936 = (10184540228 : ℤ) := join chunk9_78 chunk9_79
private theorem chunk10_40 : treeSum term 10 40960 = (-62664629945 : ℤ) := join chunk9_80 chunk9_81
private theorem chunk10_41 : treeSum term 10 41984 = (-73287415987 : ℤ) := join chunk9_82 chunk9_83
private theorem chunk10_42 : treeSum term 10 43008 = (66236057595 : ℤ) := join chunk9_84 chunk9_85
private theorem chunk10_43 : treeSum term 10 44032 = (0 : ℤ) := join chunk9_86 chunk9_87
private theorem chunk10_44 : treeSum term 10 45056 = (0 : ℤ) := join chunk9_88 chunk9_89
private theorem chunk10_45 : treeSum term 10 46080 = (0 : ℤ) := join chunk9_90 chunk9_91
private theorem chunk10_46 : treeSum term 10 47104 = (0 : ℤ) := join chunk9_92 chunk9_93
private theorem chunk10_47 : treeSum term 10 48128 = (0 : ℤ) := join chunk9_94 chunk9_95
private theorem chunk10_48 : treeSum term 10 49152 = (0 : ℤ) := join chunk9_96 chunk9_97
private theorem chunk10_49 : treeSum term 10 50176 = (0 : ℤ) := join chunk9_98 chunk9_99
private theorem chunk10_50 : treeSum term 10 51200 = (0 : ℤ) := join chunk9_100 chunk9_101
private theorem chunk10_51 : treeSum term 10 52224 = (0 : ℤ) := join chunk9_102 chunk9_103
private theorem chunk10_52 : treeSum term 10 53248 = (0 : ℤ) := join chunk9_104 chunk9_105
private theorem chunk10_53 : treeSum term 10 54272 = (0 : ℤ) := join chunk9_106 chunk9_107
private theorem chunk10_54 : treeSum term 10 55296 = (0 : ℤ) := join chunk9_108 chunk9_109
private theorem chunk10_55 : treeSum term 10 56320 = (0 : ℤ) := join chunk9_110 chunk9_111
private theorem chunk10_56 : treeSum term 10 57344 = (0 : ℤ) := join chunk9_112 chunk9_113
private theorem chunk10_57 : treeSum term 10 58368 = (0 : ℤ) := join chunk9_114 chunk9_115
private theorem chunk10_58 : treeSum term 10 59392 = (0 : ℤ) := join chunk9_116 chunk9_117
private theorem chunk10_59 : treeSum term 10 60416 = (0 : ℤ) := join chunk9_118 chunk9_119
private theorem chunk10_60 : treeSum term 10 61440 = (0 : ℤ) := join chunk9_120 chunk9_121
private theorem chunk10_61 : treeSum term 10 62464 = (0 : ℤ) := join chunk9_122 chunk9_123
private theorem chunk10_62 : treeSum term 10 63488 = (0 : ℤ) := join chunk9_124 chunk9_125
private theorem chunk10_63 : treeSum term 10 64512 = (0 : ℤ) := join chunk9_126 chunk9_127
private theorem chunk11_0 : treeSum term 11 0 = (349410018361 : ℤ) := join chunk10_0 chunk10_1
private theorem chunk11_1 : treeSum term 11 2048 = (-685954419795 : ℤ) := join chunk10_2 chunk10_3
private theorem chunk11_2 : treeSum term 11 4096 = (295376599743 : ℤ) := join chunk10_4 chunk10_5
private theorem chunk11_3 : treeSum term 11 6144 = (276143459073 : ℤ) := join chunk10_6 chunk10_7
private theorem chunk11_4 : treeSum term 11 8192 = (-348428708064 : ℤ) := join chunk10_8 chunk10_9
private theorem chunk11_5 : treeSum term 11 10240 = (266728590581 : ℤ) := join chunk10_10 chunk10_11
private theorem chunk11_6 : treeSum term 11 12288 = (-73707596124 : ℤ) := join chunk10_12 chunk10_13
private theorem chunk11_7 : treeSum term 11 14336 = (-230025979432 : ℤ) := join chunk10_14 chunk10_15
private theorem chunk11_8 : treeSum term 11 16384 = (65755576370 : ℤ) := join chunk10_16 chunk10_17
private theorem chunk11_9 : treeSum term 11 18432 = (186978089467 : ℤ) := join chunk10_18 chunk10_19
private theorem chunk11_10 : treeSum term 11 20480 = (-166346128134 : ℤ) := join chunk10_20 chunk10_21
private theorem chunk11_11 : treeSum term 11 22528 = (-107685708725 : ℤ) := join chunk10_22 chunk10_23
private theorem chunk11_12 : treeSum term 11 24576 = (210576806360 : ℤ) := join chunk10_24 chunk10_25
private theorem chunk11_13 : treeSum term 11 26624 = (-65360866289 : ℤ) := join chunk10_26 chunk10_27
private theorem chunk11_14 : treeSum term 11 28672 = (104007131266 : ℤ) := join chunk10_28 chunk10_29
private theorem chunk11_15 : treeSum term 11 30720 = (-2161084455 : ℤ) := join chunk10_30 chunk10_31
private theorem chunk11_16 : treeSum term 11 32768 = (-136980336603 : ℤ) := join chunk10_32 chunk10_33
private theorem chunk11_17 : treeSum term 11 34816 = (53261356006 : ℤ) := join chunk10_34 chunk10_35
private theorem chunk11_18 : treeSum term 11 36864 = (-27362317984 : ℤ) := join chunk10_36 chunk10_37
private theorem chunk11_19 : treeSum term 11 38912 = (26904132893 : ℤ) := join chunk10_38 chunk10_39
private theorem chunk11_20 : treeSum term 11 40960 = (-135952045932 : ℤ) := join chunk10_40 chunk10_41
private theorem chunk11_21 : treeSum term 11 43008 = (66236057595 : ℤ) := join chunk10_42 chunk10_43
private theorem chunk11_22 : treeSum term 11 45056 = (0 : ℤ) := join chunk10_44 chunk10_45
private theorem chunk11_23 : treeSum term 11 47104 = (0 : ℤ) := join chunk10_46 chunk10_47
private theorem chunk11_24 : treeSum term 11 49152 = (0 : ℤ) := join chunk10_48 chunk10_49
private theorem chunk11_25 : treeSum term 11 51200 = (0 : ℤ) := join chunk10_50 chunk10_51
private theorem chunk11_26 : treeSum term 11 53248 = (0 : ℤ) := join chunk10_52 chunk10_53
private theorem chunk11_27 : treeSum term 11 55296 = (0 : ℤ) := join chunk10_54 chunk10_55
private theorem chunk11_28 : treeSum term 11 57344 = (0 : ℤ) := join chunk10_56 chunk10_57
private theorem chunk11_29 : treeSum term 11 59392 = (0 : ℤ) := join chunk10_58 chunk10_59
private theorem chunk11_30 : treeSum term 11 61440 = (0 : ℤ) := join chunk10_60 chunk10_61
private theorem chunk11_31 : treeSum term 11 63488 = (0 : ℤ) := join chunk10_62 chunk10_63
private theorem chunk12_0 : treeSum term 12 0 = (-336544401434 : ℤ) := join chunk11_0 chunk11_1
private theorem chunk12_1 : treeSum term 12 4096 = (571520058816 : ℤ) := join chunk11_2 chunk11_3
private theorem chunk12_2 : treeSum term 12 8192 = (-81700117483 : ℤ) := join chunk11_4 chunk11_5
private theorem chunk12_3 : treeSum term 12 12288 = (-303733575556 : ℤ) := join chunk11_6 chunk11_7
private theorem chunk12_4 : treeSum term 12 16384 = (252733665837 : ℤ) := join chunk11_8 chunk11_9
private theorem chunk12_5 : treeSum term 12 20480 = (-274031836859 : ℤ) := join chunk11_10 chunk11_11
private theorem chunk12_6 : treeSum term 12 24576 = (145215940071 : ℤ) := join chunk11_12 chunk11_13
private theorem chunk12_7 : treeSum term 12 28672 = (101846046811 : ℤ) := join chunk11_14 chunk11_15
private theorem chunk12_8 : treeSum term 12 32768 = (-83718980597 : ℤ) := join chunk11_16 chunk11_17
private theorem chunk12_9 : treeSum term 12 36864 = (-458185091 : ℤ) := join chunk11_18 chunk11_19
private theorem chunk12_10 : treeSum term 12 40960 = (-69715988337 : ℤ) := join chunk11_20 chunk11_21
private theorem chunk12_11 : treeSum term 12 45056 = (0 : ℤ) := join chunk11_22 chunk11_23
private theorem chunk12_12 : treeSum term 12 49152 = (0 : ℤ) := join chunk11_24 chunk11_25
private theorem chunk12_13 : treeSum term 12 53248 = (0 : ℤ) := join chunk11_26 chunk11_27
private theorem chunk12_14 : treeSum term 12 57344 = (0 : ℤ) := join chunk11_28 chunk11_29
private theorem chunk12_15 : treeSum term 12 61440 = (0 : ℤ) := join chunk11_30 chunk11_31
private theorem chunk13_0 : treeSum term 13 0 = (234975657382 : ℤ) := join chunk12_0 chunk12_1
private theorem chunk13_1 : treeSum term 13 8192 = (-385433693039 : ℤ) := join chunk12_2 chunk12_3
private theorem chunk13_2 : treeSum term 13 16384 = (-21298171022 : ℤ) := join chunk12_4 chunk12_5
private theorem chunk13_3 : treeSum term 13 24576 = (247061986882 : ℤ) := join chunk12_6 chunk12_7
private theorem chunk13_4 : treeSum term 13 32768 = (-84177165688 : ℤ) := join chunk12_8 chunk12_9
private theorem chunk13_5 : treeSum term 13 40960 = (-69715988337 : ℤ) := join chunk12_10 chunk12_11
private theorem chunk13_6 : treeSum term 13 49152 = (0 : ℤ) := join chunk12_12 chunk12_13
private theorem chunk13_7 : treeSum term 13 57344 = (0 : ℤ) := join chunk12_14 chunk12_15
private theorem chunk14_0 : treeSum term 14 0 = (-150458035657 : ℤ) := join chunk13_0 chunk13_1
private theorem chunk14_1 : treeSum term 14 16384 = (225763815860 : ℤ) := join chunk13_2 chunk13_3
private theorem chunk14_2 : treeSum term 14 32768 = (-153893154025 : ℤ) := join chunk13_4 chunk13_5
private theorem chunk14_3 : treeSum term 14 49152 = (0 : ℤ) := join chunk13_6 chunk13_7
private theorem chunk15_0 : treeSum term 15 0 = (75305780203 : ℤ) := join chunk14_0 chunk14_1
private theorem chunk15_1 : treeSum term 15 32768 = (-153893154025 : ℤ) := join chunk14_2 chunk14_3
private theorem chunk16_0 : treeSum term 16 0 = (-78587373822 : ℤ) := join chunk15_0 chunk15_1

/-- Ordinary (Möbius) leaves in the Legendre sieve for A247824 H2. -/
theorem ordinary_value :
    ∑ d ∈ (Icc 1 43399).filter Squarefree, moebius d * ((81744924555066 / d : ℕ) : ℤ) =
      -78587373822 := sum_eq.symm.trans chunk16_0

end Astra247824.Ordinary
-- Credit: @Medrov
theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1.H3 := Astra247824.Ordinary.ordinary_value
