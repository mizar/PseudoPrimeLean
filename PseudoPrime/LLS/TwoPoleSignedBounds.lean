/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneComparison
public import PseudoPrime.LLS.TwoPoleNegativeLogBounds
public import PseudoPrime.LLS.GammaSignedConductorRemainder

/-! # Two-pole arithmetic bounds retaining signed archimedean and conductor terms -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive nonprincipal GRH with conductor between three and an ambient
level at least 20000 and scale at least two, the two-pole Gamma arithmetic sum has
an upper real bound retaining Euler prefixes. The signed archimedean contribution
is nonpositive and the left allowance is conductor free. No 64/9 norm cost is added. -/
theorem gamma_primitive_sum_re_le_twoPole_signed {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + 419 / 50 -
          (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) *
            (∑ n ∈ B,
              Real.log n *
                AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv
      (by linarith only [hx] : 0 < x) A B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz, hr, hn]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- The ambient two-pole arithmetic upper budget with the signed remainder.
It contains half the ambient logarithm, the zero-mass constant, the pole cost and
43x^(-9/16). This common scalar upper bound feeds all three witness comparisons. -/
noncomputable def signedTwoPoleUpper (A : ℕ) (x : ℝ) : ℝ :=
  Real.log A / 2 + 419 / 50 + ((7 / 6 : ℝ) * Real.log (max 20000 A : ℕ) + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- Twice the principal ramp lower bound minus the principal Gamma upper bound
and the signed two-pole arithmetic budget. Its positivity, possibly after local
costs, is the scalar condition for prime-witness extraction. -/
noncomputable def signedTwoPoleGap (A : ℕ) (x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    signedTwoPoleUpper A x

/-- For a nonprincipal character under GRH at level q at most A and scale at
least two, its primitive Gamma arithmetic sum is at most the signed ambient
budget. Enlarge only the nonnegative conductor factor and retain max(20000,A). -/
theorem gamma_primitive_sum_re_le_signedTwoPole_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      signedTwoPoleUpper A x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hC :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_signed (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp) hx ∅ ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hC
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hmA)
  dsimp only [signedTwoPoleUpper]
  linarith only [hC, hlog]

/-- For quadratic nonprincipal GRH data at level q at most A and scale at least
four, add the actual local correction before absorbing the conductor gap. Only
the original prime-count ramp cost remains above the signed ambient budget.
This preserves the exclusion cost for negative witnesses. -/
theorem gamma_primitive_add_local_le_signedTwoPole_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      signedTwoPoleUpper A x +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hC :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_signed (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp)
      (by linarith only [hx] : 2 ≤ x) ∅ ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hC
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 2 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hlocal :=
    gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x)
      (show 1 ≤ (1 / 2 : ℝ) * Real.sqrt x by linarith only [hs])
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) (Nat.cast_le.mpr hqA)
  dsimp only [signedTwoPoleUpper]
  linarith only [hC, hlocal, hlog]

/-- At log A at least 1500, the signed gap at any admissible controlled root
is at least (821/1000)r-log(A)/2-869/50. Compare the preceding norm-based gap and
retain the nonnegative left-conductor saving. No RH is used in this scalar bound. -/
theorem signedTwoPoleGap_lower {A : ℕ} (hL : 1500 ≤ Real.log A) {r : ℝ}
    (hr : (3 / 5 : ℝ) * Real.log A + 18 ≤ r)
    (hA : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40)
    (hB : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40) :
    (821 / 1000 : ℝ) * r - Real.log A / 2 - 869 / 50 ≤ signedTwoPoleGap A (r ^ 2) := by
  have h := twoPolePrimeTrivialSeparation_lower hL hr hA hB
  have hn := mul_nonneg (Real.log_natCast_nonneg A) (Real.rpow_nonneg (sq_nonneg r) (-9 / 16 : ℝ))
  dsimp only [twoPolePrimeTrivialSeparation, twoPolePrimeTrivialUpper, signedTwoPoleGap,
    signedTwoPoleUpper] at *
  simp only [Finset.sum_empty, mul_zero, sub_zero] at h
  nlinarith only [h, hn]

/-- For L at least 1500 and root (500/821)L+c with 18<=c<=30, the scale is at
least four and both endpoint logarithms are at most L/40. Enclose all roots by
6291L/10000. This provides shared numerical data for MR and odd non-one witnesses. -/
theorem signedTwoPole_root_data {L c : ℝ} (hL : 1500 ≤ L) (hc : 18 ≤ c) (hc' : c ≤ 30) :
    let r := (500 / 821 : ℝ) * L + c;
    4 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 40 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
  let r := (500 / 821 : ℝ) * L + c
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL, hc]
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL, hc]
  have hhi : r ≤ (6291 / 10000 : ℝ) * L := by
    dsimp only [r]; linarith only [hL, hc']
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hlo, hL, sq_nonneg (r - 2)]
  have ha :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * r ^ 2)
      (show (99 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  have hb :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  rw [Real.log_pow] at ha hb
  norm_num only [Nat.cast_ofNat] at ha hb
  have hlog := twoPole_log_le_eightieth hL
  exact ⟨hx, hlo, by linarith only [ha, hlog], by linarith only [hb, hlog]⟩

/-- At log A at least 1500, root (500/821)log A+22 gives positive signed gap.
Apply the common quantitative lower bound. This leaves no numerical hypothesis
in the MR prime-base witness consumer. -/
theorem signedTwoPoleGap_shift22_pos {A : ℕ} (hL : 1500 ≤ Real.log A) :
    0 < signedTwoPoleGap A (((500 / 821 : ℝ) * Real.log A + 22) ^ 2) := by
  have hd := signedTwoPole_root_data hL (c := 22) (by norm_num only) (by norm_num only)
  have h := signedTwoPoleGap_lower hL hd.2.1 hd.2.2.1 hd.2.2.2
  linarith only [h]

/-- At log A at least 1500, root (500/821)log A+23 gives signed gap greater
than one. The spare unit pays the prime-two cost in the odd non-one comparison. -/
theorem signedTwoPoleGap_shift23_gt_one {A : ℕ} (hL : 1500 ≤ Real.log A) :
    1 < signedTwoPoleGap A (((500 / 821 : ℝ) * Real.log A + 23) ^ 2) := by
  have hd := signedTwoPole_root_data hL (c := 23) (by norm_num only) (by norm_num only)
  have h := signedTwoPoleGap_lower hL hd.2.1 hd.2.2.1 hd.2.2.2
  linarith only [h]

/-- For any nonprincipal GRH character at level q at most A and scale at least
two, positive signed gap excludes value one at every small prime. Full prime
triviality makes the actual local correction nonpositive. This is the MR interface. -/
theorem prime_trivial_false_of_signedTwoPoleGap {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) (hgap : 0 < signedTwoPoleGap A x) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have hx0 : 0 < x := by linarith only [hx]
  have hC := gamma_primitive_sum_re_le_signedTwoPole_ambient χ hne hqA hGRH hx
  have hlocal :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx0
      (fun p hp ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hp).le)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb ↦ ht p hp hb)
  dsimp only [signedTwoPoleGap] at hgap
  linarith only [hC, hlocal, hP, hT, hN, hgap]

/-- For quadratic nonprincipal GRH data at scale at least four, signed gap
larger than the original level's prime-count local cost excludes value one on
all eligible unit primes. Combine the actual local budget and ramp comparison. -/
theorem unit_prime_trivial_false_of_signedTwoPoleGap {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        signedTwoPoleGap A x) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have hC := gamma_primitive_add_local_le_signedTwoPole_ambient χ hquad hne hqA hGRH hx
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
  dsimp only [signedTwoPoleGap] at hgap
  linarith only [hC, hP, hT, hN, hgap]

/-- Under the signed-gap and quadratic GRH assumptions, a prime below the
cutoff does not divide the original level and has value minus one. Negate unit
prime triviality and use quadraticity. This is the generic negative-witness API. -/
theorem exists_prime_neg_one_of_signedTwoPoleGap {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        signedTwoPoleGap A x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra h
    apply unit_prime_trivial_false_of_signedTwoPoleGap χ hquad hne hqA hGRH hx hgap
    intro p hp hd hb
    exact Classical.byContradiction (fun hv ↦ h ⟨p, hp, hd, hb, hv⟩)
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

theorem exists_odd_prime_ne_one_le_signedTwoPole_shift23 {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 23) ^ 2 ∧ χ p ≠ 1 := by
  let r := (500 / 821 : ℝ) * Real.log A + 23
  let x := r ^ 2
  have hd := signedTwoPole_root_data hL (c := 23) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ x := hd.1
  have hx : 2 ≤ x := by linarith only [hx4]
  have hxpos : 0 < x := by linarith only [hx]
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hs : Real.sqrt x = r := Real.sqrt_sq hr.le
  have hlocal : (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
    have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    rw [hs]
    have hroot : (3 / 5 : ℝ) * Real.log A + 18 ≤ r := hd.2.1
    have hlog : Real.log ((99 / 40 : ℝ) * x) ≤ Real.log A / 40 := hd.2.2.1
    linarith only [ht, hroot, hlog, hL]
  have hsep := signedTwoPoleGap_shift23_gt_one hL
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hC := gamma_primitive_sum_re_le_signedTwoPole_ambient χ hne hqA hGRH hx
  apply
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hxpos
      (show 1 ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  dsimp only [signedTwoPoleGap] at hsep
  nlinarith only [hP, hT, hC, hsep, hlocal]

end PseudoPrime.LLS
