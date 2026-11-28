/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaWidth
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaWidth
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth

/-! # Physical endpoint bounds for the K141 Gamma term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three endpoint numerators over the common denominator two. -/
@[expose]
public def middleK141EndpointNum (i : Fin 3) : ℕ :=
  47 + 5 * i.val

/-- Upper bounds in millionths for the normalized K141 Gamma polynomial at its endpoints. -/
@[expose]
public def middleK141EndpointCap (i : Fin 3) : ℕ :=
  ![12502, 69, 6] i

/-- Integer upper bounds before the exponential and normalization are applied. -/
private def rawCap (i : Fin 3) : ℤ :=
  ![553131069307425754342, 450342051145227500912, 5115222838597391898323] i

/-- Directed Horner evaluation certifies the three raw upper bounds. -/
private theorem raw_cap_check :
    ∀ i : Fin 3,
      (upperRow.evalInterval 31 (middleK141EndpointNum i) 2).upper ≤ rawCap i * upperRow.den := by
  decide +kernel

/-- Transfer the integer Horner bounds to the real polynomial at the endpoints. -/
private theorem raw_endpoint_le (i : Fin 3) :
    ((middleGammaUpperPoly middleK141Profile middleK141GammaRow).map (Rat.castHom ℝ)).eval
        ((middleK141EndpointNum i : ℝ) / 2) ≤
      (rawCap i : ℝ) := by
  have h := (upper_endpoint_contains (middleK141EndpointNum i) 2 (by decide)).1.2
  have hd : (0 : ℝ) < upperRow.den := Int.cast_pos.mpr (by decide +kernel)
  have hr := (Int.cast_le (R := ℝ)).mpr (raw_cap_check i)
  simpa only [Int.cast_natCast, Int.cast_ofNat] using
    h.trans ((div_le_iff₀ hd).mpr (by simpa only [Int.cast_mul] using hr))

/-- The endpoint cap includes the physical exponential and the Fourier normalization. -/
public theorem middle_k141_gamma_endpoint_le (i : Fin 3) :
    let z : ℝ := (middleK141EndpointNum i : ℝ) / 2
    (middleK141Norm : ℝ) * Real.exp (-2 * z) *
        ((middleGammaUpperPoly middleK141Profile middleK141GammaRow).map (Rat.castHom ℝ)).eval z ≤
      (middleK141EndpointCap i : ℝ) / 10 ^ 6 := by
  intro z
  have hn : ∀ j : Fin 3, 0 ≤ rawCap j := by decide +kernel
  have hc :
    ∀ j : Fin 3,
      middleK141Norm * middleGammaExpCap (40 * middleK141EndpointNum j) * (rawCap j : ℚ) ≤
        (middleK141EndpointCap j : ℚ) / 10 ^ 6 := by
    decide +kernel
  have ht : ((40 * middleK141EndpointNum i : ℕ) : ℝ) / 40 ≤ 2 * z := by
    simp only [z, Nat.cast_mul, Nat.cast_ofNat]
    linarith only
  have h :=
    middle_gamma_width_scaled (κ := middleK141Norm) (cap := (rawCap i : ℚ)) (R :=
      (middleK141EndpointCap i : ℚ) / 10 ^ 6) (y := 2 * z) (40 * middleK141EndpointNum i)
      (by decide +kernel) (by exact_mod_cast hn i) ht
      (by simpa only [Rat.cast_intCast] using raw_endpoint_le i) (hc i)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, neg_mul] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
