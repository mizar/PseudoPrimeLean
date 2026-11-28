/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.Analysis.RatComplex
import all PseudoPrime.Analysis.RatComplex
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelHeight
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalMoments
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Exact rational parts of the Gaussian midpoint evaluation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reciprocal pole at a rational height has exact rational coordinates. -/
private def midpointPole (a t : ℚ) : Analysis.RatComplex :=
  (⟨a, t⟩ : Analysis.RatComplex).inv

/-- The rational reciprocal pole embeds into the analytic expression. -/
private theorem midpoint_pole_val (a t : ℚ) :
    (midpointPole a t).val = highPoleInv (a : ℝ) (t : ℝ) := by
  rw [midpointPole, Analysis.RatComplex.val_inv, highPoleInv]
  congr 1
  apply Complex.ext
  · simp only [Analysis.RatComplex.val, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  · simp only [Analysis.RatComplex.val, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]

/-- The part of the compact square independent of the unit phase. -/
public def highMidpointSquareRat (K : HighGaussianKernel) (t : ℚ) : Analysis.RatComplex :=
  let z := midpointPole K.pole t
  let u := (Analysis.RatComplex.real 1).add ((Analysis.RatComplex.real (-(2 * K.pole))).mul z)
  let q := (z.mul z).mul (Analysis.RatComplex.horner (compactWeightRat K) u (K.degree + 1))
  (Analysis.RatComplex.real K.normalization).mul (q.mul q)

/-- Multiplying the rational compact square by its phase gives the square kernel. -/
public theorem high_midpoint_square_val (K : HighGaussianKernel) (t : ℚ) :
    highHeightKernel K (t : ℝ) =
      Complex.exp (5 * Complex.I * ((t : ℝ) : ℂ)) * (highMidpointSquareRat K t).val := by
  let z := midpointPole K.pole t
  let u := (Analysis.RatComplex.real 1).add ((Analysis.RatComplex.real (-(2 * K.pole))).mul z)
  have hu : u.val = highCompactCoord (K.pole : ℝ) (t : ℝ) := by
    simp only [u, Analysis.RatComplex.val_add, Analysis.RatComplex.val_mul,
      Analysis.RatComplex.val_real, z, midpoint_pole_val, highCompactCoord, Rat.cast_one,
      Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat, Complex.ofReal_ratCast, neg_mul, sub_eq_add_neg]
  have hq :
    (Analysis.RatComplex.horner (compactWeightRat K) u (K.degree + 1)).val =
      (highCompactPoly K).eval (highCompactCoord (K.pole : ℝ) (t : ℝ)) := by
    simp only [Analysis.RatComplex.val_horner, highCompactPoly, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, hu, ← compact_weight_cast, Complex.ofReal_ratCast]
  unfold highMidpointSquareRat highHeightKernel highCompactQuot
  simp only [Analysis.RatComplex.val_mul, Analysis.RatComplex.val_real, midpoint_pole_val]
  change
    _ =
      Complex.exp _ *
        ((K.normalization : ℂ) *
          ((highPoleInv (K.pole : ℝ) (t : ℝ) * highPoleInv (K.pole : ℝ) (t : ℝ) *
              (Analysis.RatComplex.horner (compactWeightRat K) u (K.degree + 1)).val) *
            (highPoleInv (K.pole : ℝ) (t : ℝ) * highPoleInv (K.pole : ℝ) (t : ℝ) *
              (Analysis.RatComplex.horner (compactWeightRat K) u (K.degree + 1)).val)))
  rw [hq]
  ring

/-- The array stores the translated centered coefficients once for all rational midpoints. -/
private def midpointCenteredRow (K : HighGaussianKernel) : Array ℚ :=
  let n := 2 * K.degree + 3
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let profile := headCoeffCache (n + 2) (highProfileFrom K compact)
  headAffineRow n (fun i ↦ centeredCoeff (K.pole - 1 / 2) (headCached profile) i) 5 1
    Nat.fast_choose

/-- Evaluating the padded row gives the real grouped coefficient at every stored index. -/
private theorem midpoint_centered_coeff_val (K : HighGaussianKernel) (j : ℕ)
    (hj : j < 2 * K.degree + 3 + 1) :
    ((midpointCenteredRow K)[j]?.getD 0 : ℝ) =
      principalMomentCoeff (highCenteredProfile K) 5 j := by
  let n := 2 * K.degree + 3
  let P := highCenteredProfile K
  let i : Fin (n + 1) := ⟨j, hj⟩
  have hd : P.natDegree ≤ n := by
    dsimp only [P, n]
    rw [← high_centered_rat_map]
    exact Polynomial.natDegree_map_le.trans (high_centered_rat_degree K)
  change ((midpointCenteredRow K)[i.val]?.getD 0 : ℝ) = _
  simp only [midpointCenteredRow, head_coeff_cache_eq, head_affine_row_eq, one_pow, one_mul]
  let f := fun k : ℕ ↦
    centeredCoeff (K.pole - 1 / 2) (highProfileCoeff K) k *
      ((Nat.fast_choose k j : ℚ) * 5 ^ (k - j))
  change ((∑ k : Fin (n + 1), f k : ℚ) : ℝ) = principalMomentCoeff P 5 j
  rw [Fin.sum_univ_eq_sum_range f]
  have hc (k : ℕ) : (((highCenteredRatPoly K).coeff k : ℚ) : ℝ) = P.coeff k := by
    rw [show P = (highCenteredRatPoly K).map (Rat.castHom ℝ) from (high_centered_rat_map K).symm,
      Polynomial.coeff_map, Rat.coe_castHom]
  simp only [f, ← centered_coeff_eq, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, ← Nat.choose_eq_fast_choose, hc]
  symm
  unfold principalMomentCoeff
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hd 1))
  intro k _ hk
  have hk' : P.natDegree < k :=
    Nat.lt_of_not_ge (fun h ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', zero_mul]

/-- Prepare the translated moment coefficients, including factorials, once per kernel. -/
private def midpointMomentCoeffs (K : HighGaussianKernel) : Array ℚ :=
  let row := midpointCenteredRow K
  Array.ofFn fun j : Fin (2 * K.degree + 3 + 1) ↦ row[j.val]?.getD 0 * (j.val.factorial : ℚ)

/-- Evaluate a block of real coefficients backwards from a complex accumulator. -/
private def hornerAccum (c : ℕ → ℚ) (z : Analysis.RatComplex) :
    ℕ → ℕ → Analysis.RatComplex → Analysis.RatComplex
  | 0, _, a => a
  | n + 1, i, a => hornerAccum c z n i ((Analysis.RatComplex.real (c (i + n))).add (z.mul a))

/-- The final step of the backwards evaluation adjoins the constant coefficient. -/
private theorem horner_accum_succ (c : ℕ → ℚ) (z : Analysis.RatComplex) (n i : ℕ)
    (a : Analysis.RatComplex) :
    hornerAccum c z (n + 1) i a =
      (Analysis.RatComplex.real (c i)).add (z.mul (hornerAccum c z n (i + 1) a)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [hornerAccum, ih, hornerAccum]
    rw [← Nat.add_assoc i n 1, Nat.add_right_comm i n 1]

/-- With zero as the initial accumulator, the backwards loop agrees with Horner. -/
private theorem horner_accum_eq (c : ℕ → ℚ) (z : Analysis.RatComplex) (n i : ℕ) :
    hornerAccum c z n i (Analysis.RatComplex.real 0) =
      Analysis.RatComplex.horner (fun j ↦ c (i + j)) z n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [horner_accum_succ, ih, Analysis.RatComplex.horner, Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1, Nat.add_zero]

/-- Two integer numerators over one natural denominator for complex Horner evaluation. -/
private structure HornerFraction where
  re : ℤ
  im : ℤ
  den : ℕ

/-- Normalize the two coordinates only when reading the final accumulator. -/
private def HornerFraction.value (a : HornerFraction) : Analysis.RatComplex :=
  ⟨(a.re : ℚ) / a.den, (a.im : ℚ) / a.den⟩

/-- Form the common-denominator representation of the complex argument. -/
private def hornerFraction (z : Analysis.RatComplex) : HornerFraction :=
  ⟨z.re.num * (z.im.den : ℤ), z.im.num * (z.re.den : ℤ), z.re.den * z.im.den⟩

/-- Each Horner step uses integer products and additions before any rational normalization. -/
private def hornerFractionStep (q : ℚ) (z a : HornerFraction) : HornerFraction :=
  ⟨(z.re * a.re - z.im * a.im) * (q.den : ℤ) + q.num * (z.den : ℤ) * (a.den : ℤ),
    (z.re * a.im + z.im * a.re) * (q.den : ℤ), z.den * a.den * q.den⟩

/-- The integer update represents the usual complex Horner step. -/
private theorem horner_fraction_step_value (q : ℚ) (z a : HornerFraction) (hz : z.den ≠ 0)
    (ha : a.den ≠ 0) :
    (hornerFractionStep q z a).value = (Analysis.RatComplex.real q).add (z.value.mul a.value) := by
  have hz' : (z.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz
  have ha' : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hq' : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  simp only [hornerFractionStep, HornerFraction.value, Analysis.RatComplex.add,
    Analysis.RatComplex.real, Analysis.RatComplex.mul, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul, zero_add, Analysis.RatComplex.mk.injEq]
  constructor
  · conv_rhs => rw [← q.num_div_den]
    field_simp (disch :=
      first
      | exact hz'
      | exact ha'
      | exact hq')
    ring
  · field_simp (disch :=
      first
      | exact hz'
      | exact ha'
      | exact hq')

/-- The argument's common denominator is the product of two nonzero denominators. -/
private theorem horner_fraction_den (z : Analysis.RatComplex) : (hornerFraction z).den ≠ 0 :=
  Nat.mul_ne_zero z.re.den_nz z.im.den_nz

/-- Reading the common-denominator encoding gives the original complex argument. -/
private theorem horner_fraction_value (z : Analysis.RatComplex) : (hornerFraction z).value = z := by
  cases z with
  | mk x
    y =>
    simp only [hornerFraction, HornerFraction.value, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      Analysis.RatComplex.mk.injEq]
    have hx : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
    have hy : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
    constructor
    · rw [mul_div_mul_right _ _ hy]
      exact x.num_div_den
    · rw [mul_comm (x.den : ℚ), mul_div_mul_right _ _ hx]
      exact y.num_div_den

/-- Traverse the coefficients backwards, keeping both accumulators as integers. -/
private def hornerInteger (c : ℕ → ℚ) (z : HornerFraction) : ℕ → ℕ → HornerFraction → HornerFraction
  | 0, _, a => a
  | n + 1, i, a => hornerInteger c z n i (hornerFractionStep (c (i + n)) z a)

/-- The backwards integer loop has the same value as the rational loop. -/
private theorem horner_integer_value (c : ℕ → ℚ) (z : HornerFraction) (hz : z.den ≠ 0) (n i : ℕ)
    (a : HornerFraction) (ha : a.den ≠ 0) :
    (hornerInteger c z n i a).value = hornerAccum c z.value n i a.value := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [hornerInteger, hornerAccum, ih _ (Nat.mul_ne_zero (Nat.mul_ne_zero hz ha) (c _).den_nz),
      horner_fraction_step_value _ _ _ hz ha]

/-- Evaluate in integers and read the rational result after the last step. -/
private def hornerIntegerValue (c : ℕ → ℚ) (z : Analysis.RatComplex) (n : ℕ) :
    Analysis.RatComplex :=
  (hornerInteger c (hornerFraction z) n 0 ⟨0, 0, 1⟩).value

/-- Integer Horner evaluation computes the same polynomial as rational Horner evaluation. -/
private theorem horner_integer_eq (c : ℕ → ℚ) (z : Analysis.RatComplex) (n : ℕ) :
    hornerIntegerValue c z n = Analysis.RatComplex.horner c z n := by
  rw [hornerIntegerValue, horner_integer_value _ _ (horner_fraction_den z) _ _ _ Nat.one_ne_zero,
    horner_fraction_value]
  have hzero : (HornerFraction.mk 0 0 1).value = Analysis.RatComplex.real 0 := by
    simp only [HornerFraction.value, Analysis.RatComplex.real, Int.cast_zero, zero_div]
  rw [hzero, horner_accum_eq]
  simp only [Nat.zero_add]

/-- Evaluate the centered moment from prepared coefficients and rational reciprocals. -/
private def midpointMomentWith (K : HighGaussianKernel) (coeffs : Array ℚ) (t : ℚ) :
    Analysis.RatComplex :=
  let z := midpointPole K.pole t
  let r := midpointPole (1 / 2) t
  let H := hornerIntegerValue (fun j ↦ coeffs[j]?.getD 0) z (2 * K.degree + 3 + 1)
  (H.mul z).mul r

/-- Multiply two common-denominator complex numbers without reducing either coordinate. -/
private def HornerFraction.mul (a b : HornerFraction) : HornerFraction :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re, a.den * b.den⟩

/-- Multiplication of the integer representations gives the rational complex product. -/
private theorem horner_fraction_mul_value (a b : HornerFraction) :
    (a.mul b).value = a.value.mul b.value := by
  simp only [HornerFraction.mul, HornerFraction.value, Analysis.RatComplex.mul, Int.cast_mul,
    Int.cast_sub, Int.cast_add, Nat.cast_mul, div_mul_div_comm, ← sub_div, ← add_div]

/-- The integer representation of the midpoint moment keeps a common denominator throughout. -/
private def midpointMomentFraction (K : HighGaussianKernel) (coeffs : Array ℚ) (t : ℚ) :
    HornerFraction :=
  let z := hornerFraction (midpointPole K.pole t)
  let r := hornerFraction (midpointPole (1 / 2) t)
  let H := hornerInteger (fun j ↦ coeffs[j]?.getD 0) z (2 * K.degree + 3 + 1) 0 ⟨0, 0, 1⟩
  (H.mul z).mul r

/-- Reading the integer representation recovers the existing rational midpoint moment. -/
private theorem midpoint_moment_fraction_value (K : HighGaussianKernel) (coeffs : Array ℚ) (t : ℚ) :
    (midpointMomentFraction K coeffs t).value = midpointMomentWith K coeffs t := by
  simp only [midpointMomentFraction, midpointMomentWith, horner_fraction_mul_value,
    hornerIntegerValue, horner_fraction_value]

/-- Add two common-denominator complex numbers without reducing either coordinate. -/
private def HornerFraction.add (a b : HornerFraction) : HornerFraction :=
  ⟨a.re * (b.den : ℤ) + b.re * (a.den : ℤ), a.im * (b.den : ℤ) + b.im * (a.den : ℤ), a.den * b.den⟩

/-- The integer addition represents the rational complex addition for nonzero denominators. -/
private theorem horner_fraction_add_value (a b : HornerFraction) (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    (a.add b).value = a.value.add b.value := by
  simp only [HornerFraction.add, HornerFraction.value, Analysis.RatComplex.add, Int.cast_mul,
    Int.cast_add, Int.cast_natCast, Nat.cast_mul]
  rw [div_add_div _ _ (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb),
    div_add_div _ _ (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  rw [mul_comm (b.re : ℚ), mul_comm (b.im : ℚ)]

/-- Nonzero denominators are preserved across the backwards integer loop. -/
private theorem horner_integer_den (c : ℕ → ℚ) (z : HornerFraction) (hz : z.den ≠ 0) (n i : ℕ)
    (a : HornerFraction) (ha : a.den ≠ 0) : (hornerInteger c z n i a).den ≠ 0 := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih => exact ih _ (Nat.mul_ne_zero (Nat.mul_ne_zero hz ha) (c _).den_nz)

/-- The exact midpoint moment has a nonzero common denominator. -/
private theorem midpoint_moment_fraction_den (K : HighGaussianKernel) (coeffs : Array ℚ) (t : ℚ) :
    (midpointMomentFraction K coeffs t).den ≠ 0 := by
  exact
    Nat.mul_ne_zero
      (Nat.mul_ne_zero (horner_integer_den _ _ (horner_fraction_den _) _ _ _ Nat.one_ne_zero)
        (horner_fraction_den _))
      (horner_fraction_den _)

/-- At a rational height evaluate the centered moment divided by the critical pole. -/
public def highMidpointMomentRat (K : HighGaussianKernel) (t : ℚ) : Analysis.RatComplex :=
  midpointMomentWith K (midpointMomentCoeffs K) t

/-- The rational midpoint moment is exactly the corresponding complex quotient. -/
public theorem high_midpoint_moment_val (K : HighGaussianKernel) (t : ℚ) :
    (highMidpointMomentRat K t).val =
      complexLogPolyMoment (highCenteredProfile K) 5 (Complex.I * (t : ℂ) + (K.pole : ℂ)) /
        (1 / 2 + Complex.I * (t : ℂ)) := by
  let P := highCenteredProfile K
  let n := 2 * K.degree + 3
  let s := Complex.I * (t : ℂ) + (K.pole : ℂ)
  let r := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have hd : P.natDegree ≤ n := by
    dsimp only [P, n]
    rw [← high_centered_rat_map]
    exact Polynomial.natDegree_map_le.trans (high_centered_rat_degree K)
  have pad :
    complexLogPolyMoment P 5 s =
      ∑ j ∈ Finset.range (n + 1),
        (principalMomentCoeff P 5 j : ℂ) * ((j.factorial : ℂ) / s ^ (j + 1)) := by
    rw [principal_moment_by_power]
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hd 1))
    intro j _ hj
    have hj' : P.natDegree < j :=
      Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
    have hz : principalMomentCoeff P 5 j = 0 := by
      unfold principalMomentCoeff
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Nat.choose_eq_zero_of_lt
            ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans_lt hj'),
        Nat.cast_zero, zero_mul, mul_zero]
    rw [hz, Complex.ofReal_zero, zero_mul]
  have hz : (midpointPole K.pole t).val = s⁻¹ := by
    rw [midpoint_pole_val, highPoleInv]
    simp only [s, Complex.ofReal_ratCast, add_comm (K.pole : ℂ) (Complex.I * (t : ℂ))]
  have hr : (midpointPole (1 / 2) t).val = r⁻¹ := by
    rw [midpoint_pole_val, highPoleInv]
    simp only [r, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_ratCast]
  change (highMidpointMomentRat K t).val = complexLogPolyMoment P 5 s / r
  simp only [highMidpointMomentRat, midpointMomentWith, Analysis.RatComplex.val_mul,
    horner_integer_eq, Analysis.RatComplex.val_horner, hz, hr, Finset.sum_mul, pad, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hc := midpoint_centered_coeff_val K j hj'
  simp only [midpointMomentCoeffs, Array.getElem?_ofFn, dite_eq_left hj', Option.getD_some,
    Rat.cast_mul, Rat.cast_natCast, ← Complex.ofReal_ratCast, hc, inv_pow, div_eq_mul_inv, pow_succ,
    P]
  ring_nf

/-- At rational heights, only the unit phase and the real exponential remain to be enclosed. -/
public theorem high_midpoint_rat_parts (K : HighGaussianKernel) (t : ℚ) :
    highPrincipalMultiplier K (t : ℝ) =
      Complex.exp (5 * Complex.I * (t : ℂ)) * (highMidpointSquareRat K t).val +
        4 * Complex.exp (-(5 * (K.pole : ℂ))) * (highMidpointMomentRat K t).val := by
  rw [high_principal_multiplier_centered, high_midpoint_square_val, high_midpoint_moment_val]
  simp only [Complex.ofReal_ratCast, highCenteredProfile]

/-- The midpoint error adds the two exponential enclosure errors after algebraic combination. -/
public theorem high_midpoint_enclosure (K : HighGaussianKernel) (t q : ℚ) (p : Analysis.RatComplex)
    {δ ε : ℝ} (hp : ‖Complex.exp (5 * Complex.I * (t : ℂ)) - p.val‖ ≤ δ)
    (he : |Real.exp (-(5 * (K.pole : ℝ))) - (q : ℝ)| ≤ ε) :
    let A := highMidpointSquareRat K t
    let B := highMidpointMomentRat K t
    let C := (p.mul A).add ((Analysis.RatComplex.real (4 * q)).mul B)
    ‖highPrincipalMultiplier K (t : ℝ)‖ ≤ ‖C.val‖ + δ * ‖A.val‖ + 4 * ε * ‖B.val‖ := by
  intro A B C
  let u := Complex.exp (5 * Complex.I * (t : ℂ))
  let e := Real.exp (-(5 * (K.pole : ℝ)))
  have hc : C.val = p.val * A.val + 4 * (q : ℂ) * B.val := by
    simp only [C, Analysis.RatComplex.val_add, Analysis.RatComplex.val_mul,
      Analysis.RatComplex.val_real, Rat.cast_mul, Rat.cast_ofNat]
  have hm :
    highPrincipalMultiplier K (t : ℝ) =
      C.val + (u - p.val) * A.val + 4 * ((e : ℂ) - (q : ℂ)) * B.val := by
    rw [high_midpoint_rat_parts, hc]
    simp only [A, B, u, e, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_ratCast]
    ring
  have he' : ‖(e : ℂ) - (q : ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact he
  rw [hm]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  · rw [norm_mul, norm_mul, Complex.norm_ofNat]
    exact
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' (by norm_num only)) (norm_nonneg _)

end PseudoPrime.PrimeTestBounds.MillerRabin
