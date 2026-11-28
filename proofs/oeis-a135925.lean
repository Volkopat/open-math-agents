import OMAStatements.S_oeis_a135925

-- Problem: A135925: G.f.: (x^2+x-1)*(1+2*x+S)*(1-5*x+2*x^2+(3*x-1)*S)^2*(-1+3*x+2*x^2+(1-x)*S), where S=sqrt(1-4*x).
-- Upstream: formal-conjectures statements/oeis-a135925.lean:0 (declaration OMA.S_oeis_a135925.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A135925Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 + (0) * S) = 16 * X - 216 * X ^ 2 + 1056 * X ^ 3 - 2152 * X ^ 4 + 1240 * X ^ 5 + 1024 * X ^ 6 - 824 * X ^ 7 - 160 * X ^ 8 + 16 * X ^ 9 + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * S) :
    (-32 * X + 496 * X ^ 2 - 2912 * X ^ 3 + 7792 * X ^ 4 - 8272 * X ^ 5 - 704 * X ^ 6 + 5264 * X ^ 7 - 480 * X ^ 8 - 384 * X ^ 9) * derivative ℚ G + (32 - 928 * X + 8000 * X ^ 2 - 28288 * X ^ 3 + 37296 * X ^ 4 + 4512 * X ^ 5 - 34288 * X ^ 6 + 3552 * X ^ 7 + 3264 * X ^ 8) * G = 2560 * X ^ 6 - 32768 * X ^ 7 + 133632 * X ^ 8 - 113664 * X ^ 9 - 366592 * X ^ 10 + 374784 * X ^ 11 + 573952 * X ^ 12 - 169984 * X ^ 13 - 456192 * X ^ 14 - 219136 * X ^ 15 - 43008 * X ^ 16 - 3072 * X ^ 17 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d72 : derivative ℚ (72 : ℚ⟦X⟧) = 0 := dnum 72
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d184 : derivative ℚ (184 : ℚ⟦X⟧) = 0 := dnum 184
  have d216 : derivative ℚ (216 : ℚ⟦X⟧) = 0 := dnum 216
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d720 : derivative ℚ (720 : ℚ⟦X⟧) = 0 := dnum 720
  have d824 : derivative ℚ (824 : ℚ⟦X⟧) = 0 := dnum 824
  have d1016 : derivative ℚ (1016 : ℚ⟦X⟧) = 0 := dnum 1016
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1056 : derivative ℚ (1056 : ℚ⟦X⟧) = 0 := dnum 1056
  have d1240 : derivative ℚ (1240 : ℚ⟦X⟧) = 0 := dnum 1240
  have d2152 : derivative ℚ (2152 : ℚ⟦X⟧) = 0 := dnum 2152
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (1) * G = (16 * X - 216 * X ^ 2 + 1056 * X ^ 3 - 2152 * X ^ 4 + 1240 * X ^ 5 + 1024 * X ^ 6 - 824 * X ^ 7 - 160 * X ^ 8 + 16 * X ^ 9 : ℚ⟦X⟧) + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 : ℚ⟦X⟧) * G) = (0) * G + (1) * derivative ℚ G := by
    simp
  have hR : derivative ℚ ((16 * X - 216 * (X * X) + 1056 * (X * X * X) - 2152 * (X * X * X * X) + 1240 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) - 824 * (X * X * X * X * X * X * X) - 160 * (X * X * X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-16 * X + 184 * (X * X) - 720 * (X * X * X) + 1016 * (X * X * X * X) - 72 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 72 * (X * X * X * X * X * X * X) + 48 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      16 - 432 * X + 3168 * X ^ 2 - 8608 * X ^ 3 + 6200 * X ^ 4 + 6144 * X ^ 5 - 5768 * X ^ 6 - 1280 * X ^ 7 + 144 * X ^ 8 + (-16 + 368 * X - 2160 * X ^ 2 + 4064 * X ^ 3 - 360 * X ^ 4 - 3840 * X ^ 5 + 504 * X ^ 6 + 384 * X ^ 7) * S + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * derivative ℚ S := by
    simp [Derivation.leibniz, d16, d48, d72, d160, d184, d216, d640, d720, d824, d1016, d1024, d1056, d1240, d2152]
    ring
  have hk2 : (1 : ℚ⟦X⟧) * G = (16 * X - 216 * (X * X) + 1056 * (X * X * X) - 2152 * (X * X * X * X) + 1240 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) - 824 * (X * X * X * X * X * X * X) - 160 * (X * X * X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-16 * X + 184 * (X * X) - 720 * (X * X * X) + 1016 * (X * X * X * X) - 72 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 72 * (X * X * X * X * X * X * X) + 48 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (0) * G + (1) * derivative ℚ G =
      16 - 432 * X + 3168 * X ^ 2 - 8608 * X ^ 3 + 6200 * X ^ 4 + 6144 * X ^ 5 - 5768 * X ^ 6 - 1280 * X ^ 7 + 144 * X ^ 8 + (-16 + 368 * X - 2160 * X ^ 2 + 4064 * X ^ 3 - 360 * X ^ 4 - 3840 * X ^ 5 + 504 * X ^ 6 + 384 * X ^ 7) * S + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) ^ 2 * S * hdS - 2 * (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) ^ 2 * derivative ℚ S * hS -
      (2 * (-16 + 368 * X - 2160 * X ^ 2 + 4064 * X ^ 3 - 360 * X ^ 4 - 3840 * X ^ 5 + 504 * X ^ 6 + 384 * X ^ 7) * (1 - 4 * X) + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * (-4)) * hk + 2 * (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * (1 - 4 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 + (0) * S) = 16 * X - 216 * X ^ 2 + 1056 * X ^ 3 - 2152 * X ^ 4 + 1240 * X ^ 5 + 1024 * X ^ 6 - 824 * X ^ 7 - 160 * X ^ 8 + 16 * X ^ 9 + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * S) :
    (30715031990396 * X ^ 2 - 291262905844111 * X ^ 3 + 805570866653979 * X ^ 4 - 393057731655406 * X ^ 5 - 539125155360312 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-402839205741004 * X + 3871921961915520 * X ^ 2 - 10908349380844896 * X ^ 3 + 5543128323534662 * X ^ 4 + 7817032085282484 * X ^ 5) * derivative ℚ G + (402839205741004 - 8480945375678382 * X + 34105003812730494 * X ^ 2 - 22430197569055514 * X ^ 3 - 32075544070681224 * X ^ 4) * G =
      17483921103890240 * X ^ 6 - 96203187527862528 * X ^ 7 + 26860851665524032 * X ^ 8 + 267411638401515712 * X ^ 9 + 107522236010828544 * X ^ 10 - 82029355854002112 * X ^ 11 - 56627815207112768 * X ^ 12 - 8628263825301312 * X ^ 13 := by
  have h := key S G hS hG
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have d496 : derivative ℚ (496 : ℚ⟦X⟧) = 0 := dnum 496
  have d704 : derivative ℚ (704 : ℚ⟦X⟧) = 0 := dnum 704
  have d928 : derivative ℚ (928 : ℚ⟦X⟧) = 0 := dnum 928
  have d2560 : derivative ℚ (2560 : ℚ⟦X⟧) = 0 := dnum 2560
  have d2912 : derivative ℚ (2912 : ℚ⟦X⟧) = 0 := dnum 2912
  have d3072 : derivative ℚ (3072 : ℚ⟦X⟧) = 0 := dnum 3072
  have d3264 : derivative ℚ (3264 : ℚ⟦X⟧) = 0 := dnum 3264
  have d3552 : derivative ℚ (3552 : ℚ⟦X⟧) = 0 := dnum 3552
  have d4512 : derivative ℚ (4512 : ℚ⟦X⟧) = 0 := dnum 4512
  have d5264 : derivative ℚ (5264 : ℚ⟦X⟧) = 0 := dnum 5264
  have d7792 : derivative ℚ (7792 : ℚ⟦X⟧) = 0 := dnum 7792
  have d8000 : derivative ℚ (8000 : ℚ⟦X⟧) = 0 := dnum 8000
  have d8272 : derivative ℚ (8272 : ℚ⟦X⟧) = 0 := dnum 8272
  have d28288 : derivative ℚ (28288 : ℚ⟦X⟧) = 0 := dnum 28288
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d34288 : derivative ℚ (34288 : ℚ⟦X⟧) = 0 := dnum 34288
  have d37296 : derivative ℚ (37296 : ℚ⟦X⟧) = 0 := dnum 37296
  have d43008 : derivative ℚ (43008 : ℚ⟦X⟧) = 0 := dnum 43008
  have d113664 : derivative ℚ (113664 : ℚ⟦X⟧) = 0 := dnum 113664
  have d133632 : derivative ℚ (133632 : ℚ⟦X⟧) = 0 := dnum 133632
  have d169984 : derivative ℚ (169984 : ℚ⟦X⟧) = 0 := dnum 169984
  have d219136 : derivative ℚ (219136 : ℚ⟦X⟧) = 0 := dnum 219136
  have d366592 : derivative ℚ (366592 : ℚ⟦X⟧) = 0 := dnum 366592
  have d374784 : derivative ℚ (374784 : ℚ⟦X⟧) = 0 := dnum 374784
  have d456192 : derivative ℚ (456192 : ℚ⟦X⟧) = 0 := dnum 456192
  have d573952 : derivative ℚ (573952 : ℚ⟦X⟧) = 0 := dnum 573952
  have hL : derivative ℚ ((-32 * X + 496 * (X * X) - 2912 * (X * X * X) + 7792 * (X * X * X * X) - 8272 * (X * X * X * X * X) - 704 * (X * X * X * X * X * X) + 5264 * (X * X * X * X * X * X * X) - 480 * (X * X * X * X * X * X * X * X) - 384 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (32 - 928 * X + 8000 * (X * X) - 28288 * (X * X * X) + 37296 * (X * X * X * X) + 4512 * (X * X * X * X * X) - 34288 * (X * X * X * X * X * X) + 3552 * (X * X * X * X * X * X * X) + 3264 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-32 + 992 * X - 8736 * X ^ 2 + 31168 * X ^ 3 - 41360 * X ^ 4 - 4224 * X ^ 5 + 36848 * X ^ 6 - 3840 * X ^ 7 - 3456 * X ^ 8) * derivative ℚ G + (-32 * X + 496 * X ^ 2 - 2912 * X ^ 3 + 7792 * X ^ 4 - 8272 * X ^ 5 - 704 * X ^ 6 + 5264 * X ^ 7 - 480 * X ^ 8 - 384 * X ^ 9) * derivative ℚ (derivative ℚ G) + (-928 + 16000 * X - 84864 * X ^ 2 + 149184 * X ^ 3 + 22560 * X ^ 4 - 205728 * X ^ 5 + 24864 * X ^ 6 + 26112 * X ^ 7) * G + (32 - 928 * X + 8000 * X ^ 2 - 28288 * X ^ 3 + 37296 * X ^ 4 + 4512 * X ^ 5 - 34288 * X ^ 6 + 3552 * X ^ 7 + 3264 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d32, d384, d480, d496, d704, d928, d2912, d3264, d3552, d4512, d5264, d7792, d8000, d8272, d28288, d34288, d37296]
    ring
  have hRd : derivative ℚ (2560 * (X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X) + 133632 * (X * X * X * X * X * X * X * X) - 113664 * (X * X * X * X * X * X * X * X * X) - 366592 * (X * X * X * X * X * X * X * X * X * X) + 374784 * (X * X * X * X * X * X * X * X * X * X * X) + 573952 * (X * X * X * X * X * X * X * X * X * X * X * X) - 169984 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 456192 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 219136 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 43008 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 3072 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) = 15360 * X ^ 5 - 229376 * X ^ 6 + 1069056 * X ^ 7 - 1022976 * X ^ 8 - 3665920 * X ^ 9 + 4122624 * X ^ 10 + 6887424 * X ^ 11 - 2209792 * X ^ 12 - 6386688 * X ^ 13 - 3287040 * X ^ 14 - 688128 * X ^ 15 - 52224 * X ^ 16 := by
    simp [Derivation.leibniz, d2560, d3072, d32768, d43008, d113664, d133632, d169984, d219136, d366592, d374784, d456192, d573952]
    ring
  have h2 : (-32 * X + 496 * (X * X) - 2912 * (X * X * X) + 7792 * (X * X * X * X) - 8272 * (X * X * X * X * X) - 704 * (X * X * X * X * X * X) + 5264 * (X * X * X * X * X * X * X) - 480 * (X * X * X * X * X * X * X * X) - 384 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (32 - 928 * X + 8000 * (X * X) - 28288 * (X * X * X) + 37296 * (X * X * X * X) + 4512 * (X * X * X * X * X) - 34288 * (X * X * X * X * X * X) + 3552 * (X * X * X * X * X * X * X) + 3264 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2560 * (X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X) + 133632 * (X * X * X * X * X * X * X * X) - 113664 * (X * X * X * X * X * X * X * X * X) - 366592 * (X * X * X * X * X * X * X * X * X * X) + 374784 * (X * X * X * X * X * X * X * X * X * X * X) + 573952 * (X * X * X * X * X * X * X * X * X * X * X * X) - 169984 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 456192 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 219136 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 43008 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 3072 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-32 + 992 * X - 8736 * X ^ 2 + 31168 * X ^ 3 - 41360 * X ^ 4 - 4224 * X ^ 5 + 36848 * X ^ 6 - 3840 * X ^ 7 - 3456 * X ^ 8) * derivative ℚ G + (-32 * X + 496 * X ^ 2 - 2912 * X ^ 3 + 7792 * X ^ 4 - 8272 * X ^ 5 - 704 * X ^ 6 + 5264 * X ^ 7 - 480 * X ^ 8 - 384 * X ^ 9) * derivative ℚ (derivative ℚ G) + (-928 + 16000 * X - 84864 * X ^ 2 + 149184 * X ^ 3 + 22560 * X ^ 4 - 205728 * X ^ 5 + 24864 * X ^ 6 + 26112 * X ^ 7) * G + (32 - 928 * X + 8000 * X ^ 2 - 28288 * X ^ 3 + 37296 * X ^ 4 + 4512 * X ^ 5 - 34288 * X ^ 6 + 3552 * X ^ 7 + 3264 * X ^ 8) * derivative ℚ G = 15360 * X ^ 5 - 229376 * X ^ 6 + 1069056 * X ^ 7 - 1022976 * X ^ 8 - 3665920 * X ^ 9 + 4122624 * X ^ 10 + 6887424 * X ^ 11 - 2209792 * X ^ 12 - 6386688 * X ^ 13 - 3287040 * X ^ 14 - 688128 * X ^ 15 - 52224 * X ^ 16 := by
    rw [← hL, h2, hRd]
  have hfull : (32 - 368 * X + 1440 * X ^ 2 - 2032 * X ^ 3 + 144 * X ^ 4 + 1280 * X ^ 5 - 144 * X ^ 6 - 96 * X ^ 7) * ((30715031990396 * X ^ 2 - 291262905844111 * X ^ 3 + 805570866653979 * X ^ 4 - 393057731655406 * X ^ 5 - 539125155360312 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-402839205741004 * X + 3871921961915520 * X ^ 2 - 10908349380844896 * X ^ 3 + 5543128323534662 * X ^ 4 + 7817032085282484 * X ^ 5) * derivative ℚ G + (402839205741004 - 8480945375678382 * X + 34105003812730494 * X ^ 2 - 22430197569055514 * X ^ 3 - 32075544070681224 * X ^ 4) * G - (17483921103890240 * X ^ 6 - 96203187527862528 * X ^ 7 + 26860851665524032 * X ^ 8 + 267411638401515712 * X ^ 9 + 107522236010828544 * X ^ 10 - 82029355854002112 * X ^ 11 - 56627815207112768 * X ^ 12 - 8628263825301312 * X ^ 13)) = 0 := by
    linear_combination (-30715031990396 * X + 168402777882527 * X ^ 2 - 131959755123871 * X ^ 3 - 134781288840078 * X ^ 4) * hd + (402839205741004 - 2321995202932296 * X + 1957174124880766 * X ^ 2 + 2021648665740660 * X ^ 3) * h
  have hg : (32 - 368 * X + 1440 * X ^ 2 - 2032 * X ^ 3 + 144 * X ^ 4 + 1280 * X ^ 5 - 144 * X ^ 6 - 96 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (32 : ℚ⟦X⟧) = 32 := cnum 32
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 + (0) * S) = 16 * X - 216 * X ^ 2 + 1056 * X ^ 3 - 2152 * X ^ 4 + 1240 * X ^ 5 + 1024 * X ^ 6 - 824 * X ^ 7 - 160 * X ^ 8 + 16 * X ^ 9 + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 30715031990396 + derivative ℚ (derivative ℚ G) * X * X * X * C (-291262905844111) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 805570866653979 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-393057731655406) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-539125155360312) + derivative ℚ G * X * C (-402839205741004) +
      derivative ℚ G * X * X * C 3871921961915520 + derivative ℚ G * X * X * X * C (-10908349380844896) +
      derivative ℚ G * X * X * X * X * C 5543128323534662 + derivative ℚ G * X * X * X * X * X * C 7817032085282484 +
      G * C 402839205741004 + G * X * C (-8480945375678382) +
      G * X * X * C 34105003812730494 + G * X * X * X * C (-22430197569055514) +
      G * X * X * X * X * C (-32075544070681224) =
      C 17483921103890240 * X * X * X * X * X * X + C (-96203187527862528) * X * X * X * X * X * X * X +
      C 26860851665524032 * X * X * X * X * X * X * X * X + C 267411638401515712 * X * X * X * X * X * X * X * X * X +
      C 107522236010828544 * X * X * X * X * X * X * X * X * X * X + C (-82029355854002112) * X * X * X * X * X * X * X * X * X * X * X +
      C (-56627815207112768) * X * X * X * X * X * X * X * X * X * X * X * X + C (-8628263825301312) * X * X * X * X * X * X * X * X * X * X * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 + (0) * S) = 16 * X - 216 * X ^ 2 + 1056 * X ^ 3 - 2152 * X ^ 4 + 1240 * X ^ 5 + 1024 * X ^ 6 - 824 * X ^ 7 - 160 * X ^ 8 + 16 * X ^ 9 + (-16 * X + 184 * X ^ 2 - 720 * X ^ 3 + 1016 * X ^ 4 - 72 * X ^ 5 - 640 * X ^ 6 + 72 * X ^ 7 + 48 * X ^ 8) * S) (m : ℕ) :
    30715031990396 * ((m : ℚ) + 14) * ((m : ℚ) + 13) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-291262905844111) * ((m : ℚ) + 13) * ((m : ℚ) + 12) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      805570866653979 * ((m : ℚ) + 12) * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-393057731655406) * ((m : ℚ) + 11) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-539125155360312) * ((m : ℚ) + 10) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-402839205741004) * ((m : ℚ) + 14) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3871921961915520 * ((m : ℚ) + 13) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-10908349380844896) * ((m : ℚ) + 12) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      5543128323534662 * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 7817032085282484 * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      402839205741004 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-8480945375678382) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      34105003812730494 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22430197569055514) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-32075544070681224) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A135925Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a135925.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 14, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  rw [e1, e2, e3, e4]
  have r := A135925Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG + ((-1 + 24 * PowerSeries.X - 161 * PowerSeries.X ^ 2 + 405 * PowerSeries.X ^ 3 - 306 * PowerSeries.X ^ 4 - 165 * PowerSeries.X ^ 5 + 188 * PowerSeries.X ^ 6 + 32 * PowerSeries.X ^ 7) + (2 - 24 * PowerSeries.X + 94 * PowerSeries.X ^ 2 - 134 * PowerSeries.X ^ 3 + 20 * PowerSeries.X ^ 4 + 70 * PowerSeries.X ^ 5 - 12 * PowerSeries.X ^ 6) * S + (-1 + 8 * PowerSeries.X - 21 * PowerSeries.X ^ 2 + 17 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 4 - 9 * PowerSeries.X ^ 5) * S ^ 2) * hS) m
  push_cast
  linear_combination r
