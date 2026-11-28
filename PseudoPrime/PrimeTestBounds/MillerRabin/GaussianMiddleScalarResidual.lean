/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePairMassBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleRange

/-! # Conductor normalization at the direct middle cutoff -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the squared direct cutoff the positive radius is recovered by
exponentiating half its logarithm. -/
public theorem direct_middle_exp_half {L : ℝ} (hL : 0 < L) :
    Real.exp (Real.log ((gaussianDirectScale * L) ^ 2) / 2) = gaussianDirectScale * L := by
  have hρ : 0 < gaussianDirectScale := by norm_num only [gaussianDirectScale]
  rw [Real.log_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num only : (2 : ℝ) ≠ 0),
    Real.exp_log (mul_pos hρ hL)]

/-- At direct cutoff, the reflected conductor term has rate `a - 1/2`.
This identity moves its entire dependence on the logarithm of the input
into the exponential rate before any coefficient calculation. -/
public theorem direct_middle_reflected {L x a b κ v : ℝ}
    (hx : Real.exp (x / 2) = gaussianDirectScale * L) :
    (2 * L) * (κ * Real.exp (-a * (x + b))) * v =
      Real.exp (-(a - 1 / 2) * x) * ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * v) := by
  have hρ : gaussianDirectScale ≠ 0 := by norm_num only [gaussianDirectScale]
  have hL : L = Real.exp (x / 2) / gaussianDirectScale := by
    rw [hx, mul_comm gaussianDirectScale L, mul_div_cancel_right₀ _ hρ]
  rw [hL, show -a * (x + b) = -(a - 1 / 2) * x + (-a * b) - x / 2 by ring, Real.exp_sub,
    Real.exp_add]
  field_simp [ne_of_gt (Real.exp_pos (x / 2))]

/-- Rewrite the linear conductor cost in the exponential coordinate of the
direct cutoff. The same factor is shared by both middle kernels. -/
public theorem direct_middle_conductor {L x : ℝ} (hx : Real.exp (x / 2) = gaussianDirectScale * L) :
    3 / 8 * L = (3 / 8 / gaussianDirectScale) * Real.exp (x / 2) := by
  have hρ : gaussianDirectScale ≠ 0 := by norm_num only [gaussianDirectScale]
  rw [hx]
  field_simp [hρ]

/-- At the direct cutoff an inequality forced by passage bounds the scalar
residual from above. The conductor is absorbed into the slope and a separate
profile at rate `a - 1/2`. All additive budgets may retain their signs. -/
public theorem direct_middle_residual_le {L x a b κ v E s β C D : ℝ}
    (hx : Real.exp (x / 2) = gaussianDirectScale * L)
    (h :
      Real.exp (x / 2) * s - β * (x / 2) ^ 2 + Real.exp (-a * x) * E -
          (2 * L) * (κ * Real.exp (-a * (x + b))) * v ≤
        3 / 8 * L + C + D) :
    (s - 3 / 8 / gaussianDirectScale) * Real.exp (x / 2) - β / 4 * x ^ 2 + Real.exp (-a * x) * E -
        Real.exp (-(a - 1 / 2) * x) * ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * v) ≤
      C + D := by
  rw [direct_middle_reflected hx, direct_middle_conductor hx] at h
  have he : β * (x / 2) ^ 2 = β / 4 * x ^ 2 := by ring
  rw [he] at h
  nlinarith only [h]

/-- For K141, passage at the direct cutoff bounds the residual in the coordinate
used for the middle interval certificates. The pole and Euler costs retain their signs. -/
public theorem middle_k141_direct_residual_of_pass
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK141Norm : ℝ)
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK141Scale : ℝ)
    let G :=
      23 / 100 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 32) -
          κ *
            (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
              (-(1 / 2) : ℝ) ^ 32) +
        1 / 10 ^ 6
    ((7215924929 / 10 ^ 10) - 3 / 8 / gaussianDirectScale) * Real.exp (x / 2) -
            (61 / 1000) / 4 * x ^ 2 +
          Real.exp (-a * x) * E.eval x -
        Real.exp (-(a - 1 / 2) * x) *
          ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * B.eval z) ≤
      76739 / 10 ^ 6 + 3 * G + 3 * (30 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK141Kernel 2 16 ((1 / 2 : ℝ) : ℂ)).re +
        1 / 10 := by
  intro x a b z κ B M P E G
  have hL₀ := ((by norm_num only : (0 : ℝ) < 42410).trans_le hL.1)
  have hx : Real.exp (x / 2) = gaussianDirectScale * Real.log n := direct_middle_exp_half hL₀
  have hs : Real.exp x = (gaussianDirectScale * Real.log n) ^ 2 :=
    Real.exp_log (pow_pos (mul_pos (by norm_num only [gaussianDirectScale]) hL₀) _)
  have hr := gaussian_k141_log_range hL
  have h :=
    middle_k141_scalar_of_pass hGRH hn ho hu hprod hp hq hrOdd hr.1 hr.2
      (fun l hl hle ↦ hpass l hl (hs ▸ hle))
  refine direct_middle_residual_le (b := b) (κ := κ) hx ?_
  dsimp only at h
  dsimp only [a, b, z, κ, B, M, P, E, G]
  nlinarith only [h]

/-- For K156, passage at the direct cutoff bounds the residual in the coordinate
used for the middle interval certificates. The pole and Euler costs retain their signs. -/
public theorem middle_k156_direct_residual_of_pass
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (400000 : ℝ) 7000000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK156Norm : ℝ)
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK156Scale : ℝ)
    let G :=
      1 / 1000 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK156Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 52) +
        2 / 10 ^ 6
    ((721603265 / 10 ^ 9) - 3 / 8 / gaussianDirectScale) * Real.exp (x / 2) -
            (61 / 1000) / 4 * x ^ 2 +
          Real.exp (-a * x) * E.eval x -
        Real.exp (-(a - 1 / 2) * x) *
          ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * B.eval z) ≤
      94703 / 10 ^ 6 + 3 * G + 3 * (45 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK156Kernel (49 / 20) 26 ((1 / 2 : ℝ) : ℂ)).re +
        (if 29 ≤ x then 1 / 60 else 1) := by
  intro x a b z κ B M P E G
  have hL₀ := ((by norm_num only : (0 : ℝ) < 400000).trans_le hL.1)
  have hx : Real.exp (x / 2) = gaussianDirectScale * Real.log n := direct_middle_exp_half hL₀
  have hs : Real.exp x = (gaussianDirectScale * Real.log n) ^ 2 :=
    Real.exp_log (pow_pos (mul_pos (by norm_num only [gaussianDirectScale]) hL₀) _)
  have hr := gaussian_k156_log_range hL
  have h :=
    middle_k156_scalar_of_pass hGRH hn ho hu hprod hp hq hrOdd hr.1 hr.2
      (fun l hl hle ↦ hpass l hl (hs ▸ hle))
  refine direct_middle_residual_le (b := b) (κ := κ) hx ?_
  dsimp only at h
  dsimp only [a, b, z, κ, B, M, P, E, G]
  nlinarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
