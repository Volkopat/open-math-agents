import OMAReductions.R_Fermat_fermat_number_are_composite_R1_H2_R1

-- 52 Fermat numbers F_n with 21 <= n <= 298 are composite.
-- Each case is a factor of the form k * 2^m + 1 (such factors are tabulated in the literature on Fermat numbers;
-- the ones used here were recomputed and rechecked outside Lean). The Lean proof is original: 2^(2^n) modulo the
-- factor d is obtained by n modular squarings, proved equal to the true power, and evaluated by the kernel; the
-- result d - 1 shows that d divides F_n, and d is far smaller than F_n.
-- Known cases, not progress on the open question for all n.

namespace OMA.FermatComposite2

/-- `k` modular squarings of `x`. -/
def sq (d : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => sq d k (x * x % d)

lemma sq_spec (d : ℕ) : ∀ k x : ℕ, sq d k x % d = x ^ (2 ^ k) % d := by
  intro k
  induction k with
  | zero => intro x; simp [sq]
  | succ k ih =>
    intro x
    rw [sq, ih, pow_succ, pow_mul', Nat.pow_mod (x ^ 2) (2 ^ k) d, pow_two]

lemma comp (n d : ℕ) (h : 2 ≤ d ∧ d < 2 ^ 512 ∧ 9 ≤ n ∧ sq d n 2 % d = d - 1) :
    ¬ Prime n.fermatNumber := by
  obtain ⟨h1, h2, hn, h3⟩ := h
  rw [← Nat.prime_iff]
  intro hp
  have hpow : 2 ^ 512 ≤ 2 ^ 2 ^ n := by
    apply Nat.pow_le_pow_right (by norm_num)
    calc 512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hF : n.fermatNumber = 2 ^ 2 ^ n + 1 := rfl
  have hd : d ∣ n.fermatNumber := by
    rw [hF]
    apply Nat.dvd_of_mod_eq_zero
    have h1' : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, ← sq_spec d n 2, h3, h1', Nat.sub_add_cancel (by omega), Nat.mod_self]
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · omega
  · omega

theorem listed (n : ℕ) (hn : n ∈ ({21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 42, 43, 48, 52, 55, 58, 61, 62, 63, 64, 66, 71, 72, 73, 75, 77, 81, 91, 99, 107, 117, 122, 125, 142, 144, 146, 147, 150, 207, 226, 228, 250, 255, 267, 268, 284, 298} : Finset ℕ)) :
    ¬ Prime n.fermatNumber := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact comp 21 4485296422913 (by decide +kernel)
  · exact comp 22 64658705994591851009055774868504577 (by decide +kernel)
  · exact comp 23 167772161 (by decide +kernel)
  · exact comp 25 25991531462657 (by decide +kernel)
  · exact comp 26 76861124116481 (by decide +kernel)
  · exact comp 27 151413703311361 (by decide +kernel)
  · exact comp 28 1766730974551267606529 (by decide +kernel)
  · exact comp 29 2405286912458753 (by decide +kernel)
  · exact comp 30 640126220763137 (by decide +kernel)
  · exact comp 31 46931635677864055013377 (by decide +kernel)
  · exact comp 32 25409026523137 (by decide +kernel)
  · exact comp 36 2748779069441 (by decide +kernel)
  · exact comp 37 701179711390136401921 (by decide +kernel)
  · exact comp 38 6597069766657 (by decide +kernel)
  · exact comp 39 46179488366593 (by decide +kernel)
  · exact comp 42 1529992420282859521 (by decide +kernel)
  · exact comp 43 7482850493766970889994241 (by decide +kernel)
  · exact comp 48 2408911986953445595315961857 (by decide +kernel)
  · exact comp 52 74201307460556292097 (by decide +kernel)
  · exact comp 55 4179340454199820289 (by decide +kernel)
  · exact comp 58 219055085875300925441 (by decide +kernel)
  · exact comp 61 4057181540151185357230047233 (by decide +kernel)
  · exact comp 62 12857380619375557476353 (by decide +kernel)
  · exact comp 63 1328165573307087716353 (by decide +kernel)
  · exact comp 64 2634732075339197803231444993 (by decide +kernel)
  · exact comp 66 4457323664018586376077313 (by decide +kernel)
  · exact comp 71 6450752615599935361908737 (by decide +kernel)
  · exact comp 72 1443765874709062348345951911937 (by decide +kernel)
  · exact comp 73 188894659314785808547841 (by decide +kernel)
  · exact comp 75 520961043404985083798310879233 (by decide +kernel)
  · exact comp 77 256896736668108699625062401 (by decide +kernel)
  · exact comp 81 5241902353849032101525979137 (by decide +kernel)
  · exact comp 91 14072902366596202965053244178433 (by decide +kernel)
  · exact comp 99 329244355096077565991935730125897729 (by decide +kernel)
  · exact comp 107 3346902437331832346018436558958369334886401 (by decide +kernel)
  · exact comp 117 9304595970494411110326649421962412033 (by decide +kernel)
  · exact comp 122 111331351706159727817280425663664652445286401 (by decide +kernel)
  · exact comp 125 850705917302346158658436518579420528641 (by decide +kernel)
  · exact comp 142 363618066009591119386121910507749518730588867002369 (by decide +kernel)
  · exact comp 144 3032901347000164747248857685080177164813336577 (by decide +kernel)
  · exact comp 146 13235038053749721162769301995307025251972223086886913 (by decide +kernel)
  · exact comp 147 2230074519853062314153571827264836150598041600001 (by decide +kernel)
  · exact comp 150 287733134849521512021350451441018219494761719398401 (by decide +kernel)
  · exact comp 207 2468256835981809063232453773836025757474103798450369795022913537 (by decide +kernel)
  · exact comp 226 12940774400232307101440167241769422723345829322819474790929732919623681 (by decide +kernel)
  · exact comp 228 100075322028463174917803960003016869060541080096470605049856601245089793 (by decide +kernel)
  · exact comp 250 2916513247664901672231194184906326679054237738765821706743837897199311952805889 (by decide +kernel)
  · exact comp 255 145666448260543773842852299140929388079413640709375829561637640681954717087039489 (by decide +kernel)
  · exact comp 267 671586706882722745220204604507349309522863301781696670432755461960519645471331844097 (by decide +kernel)
  · exact comp 268 2549752921046269405581793752705868564968158976255933121643003787782311874331836153857 (by decide +kernel)
  · exact comp 284 13925050619474025980350702948110983522812772222325736088332991353008465916350934514925569 (by decide +kernel)
  · exact comp 298 2012591544618472253233224340148465623118850772941945015628506763962128724166176665709196607489 (by decide +kernel)

end OMA.FermatComposite2

theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1.H1 := by
  intro n hn
  exact OMA.FermatComposite2.listed n hn
