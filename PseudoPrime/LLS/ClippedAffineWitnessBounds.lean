/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
public import PseudoPrime.LLS.PrincipalLowerWitnessBounds
public import PseudoPrime.LLS.Anchor250Separation
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.Analysis.AdaptiveReciprocalRadius

/-! # A closed affine prime-witness radius from the fully corrected principal cap -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The affine root (500/821)L+3 for the fully corrected principal comparison.
The small additive constant retains the certified full Euler prefix and the clipped-log
principal correction. It is used at logarithmic levels at least 300. -/
noncomputable def clippedAffineRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + 3

/-- For positive r and width r squared divided by twenty, the corrected joint
error numerator is the displayed quadratic polynomial plus a constant multiple of log(2 pi).
Expand the stencil and normalize. This removes all scale-dependent logarithms. -/
theorem clippedShiftError_twentieth_width_eq {r : ℝ} (hr : 0 < r) :
    clippedShiftPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 20) =
      (231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 10106397 / 494000 +
        (42 / 247 : ℝ) * Real.log (2 * Real.pi) := by
  dsimp only [clippedShiftPrincipalErrorNumerator, logShiftRampIncrement, logShiftRampEnvelope]
  rw [Real.sqrt_sq hr.le]
  field_simp (disch :=
    first
    | exact hr.ne'
    | norm_num only)
  ring

/-- For positive r at the twentieth width, the error numerator, retained atom and
constant pole cost four have the displayed polynomial upper cap. Bound exp(-1/r^2) by one
and log(2 pi) rationally. This is the uniform scalar error input for the affine root. -/
theorem clippedShiftError_twentieth_width_cap {r : ℝ} (hr : 0 < r) :
    clippedShiftPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 20) +
        Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2)) +
        4 ≤
      (231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27 := by
  have he : Real.exp (-(1 / r ^ 2)) ≤ 1 := by
    have hp := Real.exp_le_exp.mpr (neg_nonpos.mpr (one_div_nonneg.mpr (sq_nonneg r)))
    simpa only [Real.exp_zero] using hp
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hm := mul_le_mul_of_nonneg_left he hc0
  rw [clippedShiftError_twentieth_width_eq hr]
  linarith only [hm, Analysis.log_two_mul_pi_lt.le]

/-- For r at least 185, the three decreasing power errors obey the displayed
rational caps. Use monotone natural powers and exact rational inequalities.
This controls the left reflected remainder and certified Euler-prefix tail. -/
theorem clippedAffine_tail_caps {r : ℝ} (hr : 185 ≤ r) :
    r ^ (-9 / 8 : ℝ) ≤ (1 / 350 : ℝ) ∧
      1 / r ^ 3 ≤ (1 / 1000000 : ℝ) ∧ ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (1 / 17 : ℝ) := by
  have hr0 : 0 < r := by linarith only [hr]
  have h1 : r ^ (-9 / 8 : ℝ) ≤ (1 / 350 : ℝ) := by
    apply
      Analysis.negRationalPower_le_of_one_le_mul_pow hr0 (by norm_num only) 9
        (by norm_num only : (8 : ℕ) ≠ 0)
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 185) hr 9
    have hc : (1 : ℝ) ≤ (1 / 350 : ℝ) ^ 8 * (185 : ℝ) ^ 9 := by norm_num only
    exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num only))
  have h2 : 1 / r ^ 3 ≤ (1 / 1000000 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hr0 3)).mpr
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 185) hr 3
    nlinarith only [hp]
  have h3 : ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (1 / 17 : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 185) hr 2
    have hc : (1 : ℝ) ≤ (1 / 17 : ℝ) ^ 4 * ((99 / 40 : ℝ) * r ^ 2) ^ 1 := by nlinarith only [hp]
    have he :=
      Analysis.negRationalPower_le_of_one_le_mul_pow
        (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) (sq_pos_of_pos hr0)) (hi := (1 / 17 : ℝ))
        (by norm_num only) 1 (by norm_num only : (4 : ℕ) ≠ 0) hc
    simpa only [Nat.cast_one, Nat.cast_ofNat] using he
  exact ⟨h1, h2, h3⟩

/-- For ambient logarithm at least 300, the actual principal-minus-character gap
with the certified anchor saving exceeds one tenth at the affine root. Retain the positive
linear term and bound all decreasing errors at r at least 185. This proves the entire
half-line without finite input enumeration or interval certificates. -/
theorem clippedAffine_gap_gt_tenth {A : ℕ} (hL : 300 ≤ Real.log A) :
    let r := clippedAffineRoot (Real.log A)
    (1 / 10 : ℝ) <
      clippedShiftPrincipalLower (r ^ 2) (r ^ 2 / 20) - reflectedSplitUpper A (523 / 100) (r ^ 2) +
        2 * ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)) := by
  let r := clippedAffineRoot (Real.log A)
  have hr : 185 ≤ r := by
    dsimp only [r, clippedAffineRoot]; linarith only [hL]
  have hr0 : 0 < r := by linarith only [hr]
  have hm := clippedShiftPrincipalLower_ge_mass133 (r ^ 2) (r ^ 2 / 20)
  rw [Real.sqrt_sq hr0.le] at hm
  have hE := div_le_div_of_nonneg_right (clippedShiftError_twentieth_width_cap hr0) hr0.le
  have heq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hr0.ne')
  rw [heq, add_div] at hE
  have hpole : ((7 / 6 : ℝ) * Real.log A) / r ≤ (5747 / 3000 : ℝ) := by
    apply (div_le_iff₀ hr0).mpr
    dsimp only [r, clippedAffineRoot]
    linarith only
  have hrec :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 27) (by norm_num only : (0 : ℝ) < 185)
      hr
  have hlead :
    ((133 / 160 : ℝ) - 231 / 24700) * ((500 / 821 : ℝ) * 300 + 3) - 300 / 2 ≤
      ((133 / 160 : ℝ) - 231 / 24700) * r - Real.log A / 2 := by
    dsimp only [r, clippedAffineRoot]
    linarith only [hL]
  have ht := clippedAffine_tail_caps hr
  have hpow : (r ^ 2) ^ (-9 / 16 : ℝ) = r ^ (-9 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num only [Nat.cast_ofNat]
  have hmax := ambient_max_eq_of_log_ge_250 (by linarith only [hL] : 250 ≤ Real.log A)
  dsimp only [reflectedSplitUpper]
  rw [Real.sqrt_sq hr0.le, hpow, hmax, add_div]
  have he : 1 / (r ^ 2 * r) = 1 / r ^ 3 := by ring
  rw [he]
  linarith only [hm, hE, hpole, hrec, hlead, ht.1, ht.2.1, ht.2.2]

/-- For L at least 300, the square scale is at least two, its Euler cutoff is at
least 128 and the witness cutoff lies strictly below L squared. Bound the affine root by
31L/50 and compare rational squares. This discharges all analytic side conditions. -/
theorem clippedAffine_root_data {L : ℝ} (hL : 300 ≤ L) :
    2 ≤ clippedAffineRoot L ^ 2 ∧
      128 ≤ (99 / 40 : ℝ) * clippedAffineRoot L ^ 2 ∧
      (99 / 40 : ℝ) * clippedAffineRoot L ^ 2 < L ^ 2 := by
  have hr : 185 ≤ clippedAffineRoot L := by
    dsimp only [clippedAffineRoot]
    linarith only [hL]
  have hx : 2 ≤ clippedAffineRoot L ^ 2 := by
    nlinarith only [hr, sq_nonneg (clippedAffineRoot L - 185)]
  have hb : 128 ≤ (99 / 40 : ℝ) * clippedAffineRoot L ^ 2 := by
    nlinarith only [hr, sq_nonneg (clippedAffineRoot L - 185)]
  have hu : clippedAffineRoot L ≤ (31 / 50 : ℝ) * L := by
    dsimp only [clippedAffineRoot]
    linarith only [hL]
  have hs := mul_self_le_mul_self (by linarith only [hr] : 0 ≤ clippedAffineRoot L) hu
  have hsq := sq_pos_of_pos (show 0 < L by linarith only [hL])
  exact ⟨hx, hb, by nlinarith only [hs, hsq]⟩

/-- Under GRH, a nonprincipal character of level at most A with log A at least
300 cannot be trivial on all primes through (99/40) times the affine root squared.
Insert the certified anchor saving and the actual corrected principal lower cap into the
generic prefix consumer. No character-dependent numerical premise remains. -/
theorem prime_trivial_false_le_clippedAffine {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log A) :
    ¬(∀ p : ℕ,
        p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * clippedAffineRoot (Real.log A) ^ 2 → χ p = 1) := by
  let r := clippedAffineRoot (Real.log A)
  let b := (99 / 40 : ℝ) * r ^ 2
  let g := 2 * ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ))
  have hd := clippedAffine_root_data hL
  have hx0 : 0 < r ^ 2 := by linarith only [hd.1]
  have hh : 0 < r ^ 2 / 20 := div_pos hx0 (by norm_num only)
  have hhx : r ^ 2 / 20 ≤ r ^ 2 := by linarith only [hx0]
  have hK := pairedEulerPrefix_ge_anchor128 hGRH.riemann hd.2.1
  have hg : g ≤ 2 * twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊b⌋₊) := by
    dsimp only [g, b]
    linarith only [hK]
  have hm := clippedAffine_gap_gt_tenth hL
  have hp :
    0 <
      principalLowerGap A (523 / 100 - g) (r ^ 2)
        (clippedShiftPrincipalLower (r ^ 2) (r ^ 2 / 20)) := by
    dsimp only [principalLowerGap, reflectedSplitUpper, g, b] at *
    linarith only [hm]
  apply
    prime_trivial_false_of_principalLower_prefix χ hne hqA hGRH hd.1
      (clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hd.1]) hh hhx)
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed _) (Finset.Ioc 0 ⌊b⌋₊)
      _ hg hp
  intro k hk
  exact
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2).trans
      (Nat.floor_le
        (by
          dsimp only [b]; linarith only [hd.2.1] : 0 ≤ b))

/-- Under the nonprincipal GRH and ambient-level assumptions with log A at least
300, a prime with character value different from one lies through the affine cutoff.
Extract it from the proved nontriviality statement. Zero is allowed, so this is also the
character input for prime rejecting MR bases, not a negative-unit witness theorem. -/
theorem exists_prime_ne_one_le_clippedAffine {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log A) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * clippedAffineRoot (Real.log A) ^ 2 ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  apply prime_trivial_false_le_clippedAffine χ hne hqA hGRH hL
  intro p hp hb
  exact Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hb, hv⟩)

/-- The logarithm of 300 is at most 23/4. Kernel-check a rational Taylor interval.
This supplies the global tangent comparison with the adaptive reciprocal radius. -/
theorem clippedAffine_log_three_hundred_le : Real.log (300 : ℝ) ≤ (23 / 4 : ℝ) := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck 300 9 32 0 (23 / 4) = true)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at h
  exact h.2

/-- For L at least 300, the clipped affine cutoff is smaller than Y squared
whenever Y exceeds L-2log L+4. Use a logarithmic tangent at 300 to bound Y/L below by
39/40 and the affine root/L above by 6191/10000. This is a generic radius comparison. -/
theorem clippedAffine_cutoff_lt_of_adaptive_lower {L Y : ℝ} (hL : 300 ≤ L)
    (hY : L - 2 * Real.log L + 4 < Y) : (99 / 40 : ℝ) * clippedAffineRoot L ^ 2 < Y ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 300) hL0
  have hlog : 2 * Real.log L - 4 ≤ L / 40 := by
    linarith only [ht, clippedAffine_log_three_hundred_le, hL]
  have hYb : (39 / 40 : ℝ) * L < Y := by linarith only [hlog, hY]
  have hr : 0 ≤ clippedAffineRoot L := by
    dsimp only [clippedAffineRoot]; linarith only [hL]
  have hu : clippedAffineRoot L ≤ (6191 / 10000 : ℝ) * L := by
    dsimp only [clippedAffineRoot]
    linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hY0 : 0 < Y := by linarith only [hL0, hYb]
  have hp :=
    mul_pos (sub_pos.mpr hYb) (add_pos hY0 (mul_pos (by norm_num only : (0 : ℝ) < 39 / 40) hL0))
  have hsq := sq_pos_of_pos hL0
  nlinarith only [hs, hp, hsq]

/-- Under GRH, a proper unit subgroup at logarithmic level at least 300 has a prime
outside its image through the clipped affine cutoff. Pull back a nonprincipal quotient
character and apply the character bound. Nonunit primes remain valid witnesses. -/
theorem exists_prime_outside_subgroup_le_clippedAffine {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * clippedAffineRoot (Real.log q) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hz
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_le_clippedAffine (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) le_rfl hGRH hL
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- For every real L at least 300, the clipped affine cutoff is smaller than the
adaptive reciprocal cutoff. Use the proved reference-root bound to supply the generic
comparison premise. This certifies the best-interval replacement without sampled crossings. -/
theorem clippedAffine_cutoff_lt_adaptive {L : ℝ} (hL : 300 ≤ L) :
    (99 / 40 : ℝ) * clippedAffineRoot L ^ 2 < Analysis.adaptivePart2CutoffRoot L ^ 2 := by
  have ht :=
    Analysis.finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le
      (by linarith only [hL] : (639 / 100 : ℝ) ≤ L)
  have hb :=
    Analysis.adaptivePart2Root_bounds
      (show 7 ≤ Analysis.finerPart2CutoffRoot L by linarith only [ht])
  apply clippedAffine_cutoff_lt_of_adaptive_lower hL
  dsimp only [Analysis.finerPart2CutoffRoot] at hb
  linarith only [hb.1]

end PseudoPrime.LLS
