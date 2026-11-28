/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaNet
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaNet
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth

/-! # Physical endpoint bounds for the K156 Gamma term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The numerator of the physical coordinate at each of the eight cell endpoints. -/
@[expose]
public def middleK156EndpointNum (i : Fin 8) : ℤ :=
  if i.val = 7 then 135 else 55 + 2 * (i.val : ℤ)

/-- The denominator of the physical coordinate, with a quarter at the last endpoint. -/
@[expose]
public def middleK156EndpointDen (i : Fin 8) : ℤ :=
  if i.val = 7 then 4 else 2

/-- Upper bounds in millionths for the normalized K156 Gamma polynomial at its endpoints. -/
@[expose]
public def middleK156EndpointCap (i : Fin 8) : ℕ :=
  ![486, 272, 152, 85, 47, 26, 14, 13] i

/-- Integer upper bounds for the unscaled net polynomial at the endpoints. -/
private def rawCap (i : Fin 8) : ℤ :=
  ![13334415210965077162309636787, 86454670673968397846706647685, 558620468975499281338909622672,
      3596000265204303461513817149576, 23047563541723810645547466953790,
      146902442630106051239626900953569, 930366906526458904264406860482414,
      1474463490526783343974134599881495]
    i

/-- Number of fortieths of the exponential argument, rounded down. -/
private def expTicks (i : Fin 8) : ℕ :=
  ![2695, 2793, 2891, 2989, 3087, 3185, 3283, 3307] i

/-- The raw bounds are certified by directed integer Horner evaluation. -/
private theorem raw_cap_check :
    ∀ i : Fin 8,
      (netRow.evalInterval 80 (middleK156EndpointNum i) (middleK156EndpointDen i)).upper ≤
        rawCap i * netRow.den := by
  refine Fin.cases ?_ ?_
  · exact first_endpoint_tick
  · have h :
      ∀ i : Fin 7,
        (netRow.evalInterval 80 (middleK156EndpointNum i.succ)
              (middleK156EndpointDen i.succ)).upper ≤
          rawCap i.succ * netRow.den := by
      decide +kernel
    exact h

/-- The denominators of the endpoint coordinates are positive. -/
private theorem endpoint_den_pos : ∀ i : Fin 8, 0 < middleK156EndpointDen i := by decide +kernel

/-- The raw integer bounds transfer to the real polynomial. -/
private theorem raw_endpoint_le (i : Fin 8) :
    (middleK156GammaNet.map (Rat.castHom ℝ)).eval
        ((middleK156EndpointNum i : ℝ) / middleK156EndpointDen i) ≤
      (rawCap i : ℝ) := by
  have h := (net_endpoint_contains (middleK156EndpointNum i) _ (endpoint_den_pos i)).1.2
  have hd : (0 : ℝ) < netRow.den := Int.cast_pos.mpr (by decide +kernel)
  refine h.trans ((div_le_iff₀ hd).mpr ?_)
  exact_mod_cast raw_cap_check i

/-- The endpoint cap includes the physical exponential and the Fourier normalization. -/
public theorem middle_k156_gamma_endpoint_le (i : Fin 8) :
    let z : ℝ := (middleK156EndpointNum i : ℝ) / middleK156EndpointDen i
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleK156GammaNet.map (Rat.castHom ℝ)).eval z ≤
      (middleK156EndpointCap i : ℝ) / 10 ^ 6 := by
  intro z
  have ht :
    ∀ j : Fin 8,
      (expTicks j : ℚ) / 40 ≤
        (49 / 20 : ℚ) * ((middleK156EndpointNum j : ℚ) / middleK156EndpointDen j) := by
    decide +kernel
  have hn : ∀ j : Fin 8, 0 ≤ rawCap j := by decide +kernel
  have hc :
    ∀ j : Fin 8,
      middleK156Norm * middleGammaExpCap (expTicks j) * (rawCap j : ℚ) ≤
        (middleK156EndpointCap j : ℚ) / 10 ^ 6 := by
    decide +kernel
  have ht' : (expTicks i : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by
    simpa only [z, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
      Rat.cast_intCast] using (Rat.cast_le (K := ℝ)).mpr (ht i)
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := (rawCap i : ℚ)) (R :=
      (middleK156EndpointCap i : ℚ) / 10 ^ 6) (y := (49 / 20 : ℝ) * z) (expTicks i)
      (by decide +kernel) (by exact_mod_cast hn i) ht'
      (by simpa only [Rat.cast_intCast] using raw_endpoint_le i) (hc i)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, neg_mul] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
