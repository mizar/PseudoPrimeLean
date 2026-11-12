/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.CubicCharacterExclusion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterDefectSharp

/-! # Cubic character defects with a sharp prime-power cost -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For `x ≥ 1`, the normalized cubic weight lies between zero and `1/3`
through the natural cutoff. This is the weight used in the cubic defect identity. -/
private theorem cubic_weight_bounds {x : ℝ} (hx : 1 ≤ x) :
    ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      0 ≤ (1 - ((n : ℝ) / x) ^ 3) / 3 ∧ (1 - ((n : ℝ) / x) ^ 3) / 3 ≤ 1 / 3 := by
  intro n hn
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hn0 : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) hx0.le
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx0.le)
  have hr : (n : ℝ) / x ≤ 1 := (div_le_one hx0).mpr hnle
  have hp : ((n : ℝ) / x) ^ 3 ≤ 1 := pow_le_one₀ hn0 hr
  constructor <;> nlinarith only [hp, pow_nonneg hn0 3]

/-- For `x ≥ 1`, the unnormalized cubic character defect is its finite weighted
Mangoldt sum. Expand both character sums and cancel the nonzero square root. -/
private theorem cubic_defect_eq_weighted {f : ℕ} (χ : DirichletCharacter ℂ f) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * ((1 - ((n : ℝ) / x) ^ 3) / 3) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  rw [reciprocalGap_principal_re_eq_sum, reciprocalGapCharacterSum_re_eq_weighted, ←
    Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [reciprocalGapPrincipalWeight, Real.rpow_ofNat]
  field_simp [hs]

/-- For `x ≥ 1` and a character trivial on primes outside nonzero `m`, the cubic defect
is at most two thirds of the excluded-prime logarithm sum plus `37 sqrt(x)/25`.
The exact weighted identity transfers the improved unconditional prime-power bound. -/
theorem cubic_defect_le_excluded_sharp {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) ≤
      (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) + (37 / 25 : ℝ) * Real.sqrt x := by
  rw [cubic_defect_eq_weighted χ hx]
  exact
    AnalyticNumberTheory.Arithmetic.weighted_defect_le_excluded_sharp χ hm hx _
      (cubic_weight_bounds hx) hsmall

/-- Under the same hypotheses, the cubic defect retains the character-sensitive exclusion
cost and has nonprime cost at most `37 sqrt(x)/25`. This feeds sharper cubic radii. -/
theorem cubic_defect_le_sensitive_sharp {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) ≤
      AnalyticNumberTheory.Arithmetic.characterExclusionCost χ m / 3 +
        (37 / 25 : ℝ) * Real.sqrt x := by
  rw [cubic_defect_eq_weighted χ hx]
  exact
    AnalyticNumberTheory.Arithmetic.weighted_defect_le_sensitive_sharp χ hm hx _
      (cubic_weight_bounds hx) hsmall

/-- Under primitive nonprincipal GRH, the cubic separation criterion remains valid with
the nonprime error reduced to `37 sqrt(x)/25`. The strict gap combines the improved defect
with the existing principal lower bound and character upper bound. -/
theorem exists_prime_of_cubic_gap_sharp {f m : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hf : 2 ≤ f) (hm : m ≠ 0) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 1 < x)
    (hgap :
      ((5 / 13 : ℝ) * Real.log f + 257 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log f +
          122917 / 15000 +
          (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) +
          (37 / 25 : ℝ) * Real.sqrt x <
        x / 4 - 3 * Real.sqrt x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1 := by
    intro p hp hpx hpm
    by_contra hv
    exact hn ⟨p, hp, hpx, hpm, hv⟩
  have hd := cubic_defect_le_excluded_sharp χ hm hx.le ht
  have hu :=
    sqrt_mul_reciprocalGapCharacterSum_three_re_le hf hGRH hp hne (fun h ↦ hne (inv_eq_one.mp h))
      hx.le
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocalGap_principal_three_ge hGRH.riemann hx)
      (Real.sqrt_nonneg x)
  nlinarith only [hd, hu, hl, Real.sq_sqrt (zero_lt_one.trans hx).le, hgap]

/-- The cubic conductor radius with the improved nonprime error. For a logarithm
envelope `G` and excluded integer `m`, set `A = (10/13)G + 13` and return
`A + sqrt(A² + (8/5)G + 33 + (8/3)∑ log p)`. Its square bounds an outside witness. -/
noncomputable def cubicSharpRadius (G : ℝ) (m : ℕ) : ℝ :=
  ((10 / 13 : ℝ) * G + 13) +
    Real.sqrt
      ((((10 / 13 : ℝ) * G + 13) ^ 2) + (8 / 5 : ℝ) * G + 33 +
        (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p)

/-- For nonnegative `G`, the sharp cubic radius is at least 13 and satisfies its
quadratic identity. Nonnegative prime logarithms ensure the radicand is nonnegative. -/
theorem cubicSharpRadius_data {G : ℝ} (hG : 0 ≤ G) (m : ℕ) :
    13 ≤ cubicSharpRadius G m ∧
      (cubicSharpRadius G m) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 13) * cubicSharpRadius G m + (8 / 5 : ℝ) * G + 33 +
          (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
  have he : 0 ≤ ∑ p ∈ m.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p hp ↦
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hr :
    0 ≤
      (((10 / 13 : ℝ) * G + 13) ^ 2) + (8 / 5 : ℝ) * G + 33 +
        (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 13), hG, he]
  have hs := Real.sq_sqrt hr
  unfold cubicSharpRadius
  constructor
  · linarith only [hG,
      Real.sqrt_nonneg
        ((((10 / 13 : ℝ) * G + 13) ^ 2) + (8 / 5 : ℝ) * G + 33 +
          (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p)]
  · nlinarith only [hs]

/-- Under primitive nonprincipal GRH, a logarithm envelope `G` gives a prime outside `m`
within the square of the improved cubic radius. Its quadratic identity supplies the
strict gap required by the sharpened cubic witness criterion. -/
theorem exists_prime_le_cubicSharpRadius {f m : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hf : 2 ≤ f) (hm : m ≠ 0) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {G : ℝ} (hlog : Real.log f ≤ G) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (cubicSharpRadius G m) ^ 2 ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hf0 : 0 ≤ Real.log (f : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hf.trans' (by decide : 1 ≤ 2))
  have hd := cubicSharpRadius_data (hf0.trans hlog) m
  have hr : 0 ≤ cubicSharpRadius G m := (by norm_num only : (0 : ℝ) ≤ 13).trans hd.1
  have hx : 1 < (cubicSharpRadius G m) ^ 2 := by nlinarith only [hd.1]
  have hs := Real.sqrt_sq hr
  have hmul := mul_le_mul_of_nonneg_right hlog hr
  apply exists_prime_of_cubic_gap_sharp χ hf hm hGRH hp hne hx
  rw [hs]
  nlinarith only [hd.1, hd.2, hlog, hmul]

/-- For nonnegative `G`, the sharp cubic radius is strictly smaller than the previous
cubic conductor radius. The affine part decreases by 21 and the square-root part
does not increase. -/
theorem cubicSharpRadius_lt_old {G : ℝ} (hG : 0 ≤ G) (m : ℕ) :
    cubicSharpRadius G m < cubicConductorRadius G m := by
  have ha : (0 : ℝ) ≤ (10 / 13 : ℝ) * G + 13 := by linarith only [hG]
  have hab : (10 / 13 : ℝ) * G + 13 ≤ (10 / 13 : ℝ) * G + 34 := by linarith only []
  have hs := pow_le_pow_left₀ ha hab 2
  have hr :=
    Real.sqrt_le_sqrt
      (show
        (((10 / 13 : ℝ) * G + 13) ^ 2) + (8 / 5 : ℝ) * G + 33 +
            (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p ≤
          (((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 +
            (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p
        by linarith only [hs])
  unfold cubicSharpRadius cubicConductorRadius
  linarith only [hr]

/-- For nonnegative `G`, the squared sharp cubic witness bound is strictly smaller
than the previous squared bound. Both radii are nonnegative and the radii compare strictly. -/
theorem cubicSharpRadius_sq_lt_old {G : ℝ} (hG : 0 ≤ G) (m : ℕ) :
    (cubicSharpRadius G m) ^ 2 < (cubicConductorRadius G m) ^ 2 := by
  have ha : 0 ≤ cubicSharpRadius G m := by linarith only [(cubicSharpRadius_data hG m).1]
  exact pow_lt_pow_left₀ (cubicSharpRadius_lt_old hG m) ha (by decide : 2 ≠ 0)

end PseudoPrime.LLS.PaperStatements
