/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorCountBounds
public import PseudoPrime.LLS.CosetCompositeBounds

/-! # Scaled principal bounds for the explicit coset prime criterion

A logarithmic prime-factor count estimate removes the cardinality term from
the principal lower bound when the cutoff dominates the subgroup scale.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, at a level at least twenty thousand and cutoff greater than one,
the principal logarithmic sum has a lower bound whose common-factor correction is
the square root times the squared logarithm divided by three times a positive scale.
Assume the scale times the level logarithm is below the cutoff square root.
Insert the prime-factor count bound into the RH formula; the coset argument uses
the subgroup index minus one as its scale. -/
theorem principal_logWeightedSum_ge_sqrt_log_lower {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (hRH : RiemannHypothesis) {x d : ℝ} (hx : 1 < x) (hd : 0 < d)
    (hs : d * Real.log q ≤ Real.sqrt x) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
        Real.sqrt x / (3 * d) * (Real.log x) ^ 2 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x
          (1 : DirichletCharacter ℂ q)).re := by
  have hr := llsRiemannWeightedLowerBound_of_riemannHypothesis hRH x hx
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have he :=
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_le_sqrt_log_square hq
      (zero_lt_one.trans hx) hd hs
  rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedSum_one_re_eq]
  nlinarith only [hr, hm, he]

/-- Under GRH, at a level at least twenty thousand and cutoff at least one billion,
a strict gap using the scaled principal lower bound gives the least prime in any coset.
Assume a proper subgroup and that its index minus one times the level logarithm
is at most the cutoff square root. Combine the lower bound with the nonprincipal
norm estimate and the uniform composite contribution. The resulting criterion
contains no prime-factor count and is used at the radius in Theorem 1.4. -/
theorem exists_least_prime_in_coset_le_of_scaled_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) (hq : 20000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1000000000 ≤ x) (hh : 1 < H.index)
    (hs : ((H.index : ℝ) - 1) * Real.log q ≤ Real.sqrt x)
    (hgap :
      (H.index : ℝ) * ((11 / 5 : ℝ) * Real.sqrt x) + cosetNonprincipalUpper q H x <
        x - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
          Real.sqrt x / (3 * ((H.index : ℝ) - 1)) * (Real.log x) ^ 2) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ (p : ℝ) ≤ x := by
  classical
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hhR : (1 : ℝ) < H.index := by exact_mod_cast hh
  have hp := principal_logWeightedSum_ge_sqrt_log_lower hq hGRH.riemann hx1 (sub_pos.mpr hhR) hs
  have hn :=
    nonprincipal_logWeightedNorm_sum_le_explicit H ((by norm_num only : (64 : ℕ) ≤ 20000).trans hq)
      hGRH ((by norm_num only : (65536 : ℝ) ≤ 1000000000).trans hx)
  have hc := compositePrimePowerLogWeightedSum_le_explicit_root_sums hGRH.riemann hx1
  have ht :=
    mul_le_mul_of_nonneg_left (hc.trans (compositeRootSum_le hx))
      (Nat.cast_nonneg H.index : (0 : ℝ) ≤ H.index)
  apply exists_least_prime_in_coset_le_of_principal_gap H a (zero_lt_one.trans hx1)
  linarith only [hgap, hp, hn, ht]

/-- The nonexceptional radius in Theorem 1.4 for modulus q and subgroup index h.
Its square is the large-prime bound; the proof uses the maximum of this square
and one billion as a cutoff. -/
noncomputable def cosetBoundRadius (q h : ℕ) : ℝ :=
  ((h : ℝ) - 1) * Real.log q + 3 * ((h : ℝ) + 1) + (5 / 2 : ℝ) * (Real.log (Real.log q)) ^ 2

/-- For a positive modulus and index at least one, the coset bound radius is nonnegative.
Every term in its definition is nonnegative. This permits squaring radius comparisons. -/
theorem coset_bound_radius_nonneg {q h : ℕ} (hq : 1 ≤ q) (hh : 1 ≤ h) :
    0 ≤ cosetBoundRadius q h := by
  have hd : (0 : ℝ) ≤ (h : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hh)
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  unfold cosetBoundRadius
  exact
    add_nonneg
      (add_nonneg (mul_nonneg hd hl)
        (mul_nonneg (by norm_num only) (add_nonneg (Nat.cast_nonneg h) zero_le_one)))
      (mul_nonneg (by norm_num only) (sq_nonneg _))

/-- At the maximum of one billion and the squared coset radius, the cutoff square root
dominates the subgroup scale times the level logarithm. The extra radius terms
are nonnegative and the maximum contains its square. This supplies the scale
assumption in the principal estimate at the cutoff of Theorem 1.4. -/
theorem coset_scale_le_sqrt_cutoff {q h : ℕ} :
    ((h : ℝ) - 1) * Real.log q ≤ Real.sqrt (max (1000000000 : ℝ) ((cosetBoundRadius q h) ^ 2)) := by
  have hr : ((h : ℝ) - 1) * Real.log q ≤ cosetBoundRadius q h := by
    unfold cosetBoundRadius
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    nlinarith only [hh0, sq_nonneg (Real.log (Real.log q))]
  exact hr.trans (Real.le_sqrt_of_sq_le (le_max_right _ _))

/-- Uniform real gaps at the explicit coset cutoff imply Theorem 1.4 under GRH.
Use the scaled principal and nonprincipal estimates to obtain a least prime below
the maximum cutoff, then split its upper bound into the two alternatives.
The only extra input is the displayed real inequality, not a character or zero estimate. -/
theorem theorem14_of_scaled_gaps
    (hgaps :
      ∀ (q : ℕ) [NeZero q],
        20000 ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            1 < H.index →
              let x := max (1000000000 : ℝ) ((cosetBoundRadius q H.index) ^ 2)
              (H.index : ℝ) * ((11 / 5 : ℝ) * Real.sqrt x) + cosetNonprincipalUpper q H x <
                x - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
                  Real.sqrt x / (3 * ((H.index : ℝ) - 1)) * (Real.log x) ^ 2) :
    lls_theorem14 := by
  intro hGRH q _ hq H hh a
  obtain ⟨p, hp, hb⟩ :=
    exists_least_prime_in_coset_le_of_scaled_gap H a hq hGRH (le_max_left _ _) hh
      coset_scale_le_sqrt_cutoff (hgaps q hq H hh)
  refine ⟨p, hp, ?_⟩
  change (p : ℝ) ≤ (10 : ℝ) ^ 9 ∨ (p : ℝ) ≤ (cosetBoundRadius q H.index) ^ 2
  norm_num only
  exact le_max_iff.mp hb

end PseudoPrime.LLS.PaperStatements
