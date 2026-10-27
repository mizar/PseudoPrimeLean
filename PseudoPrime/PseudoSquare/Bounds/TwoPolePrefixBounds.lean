/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrincipalPrefixBounds
public import PseudoPrime.LLS.TwoPolePrimePowerPrefixSavings
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Jacobi witness bounds and negative criteria with retained Euler prefixes -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The odd non-one two-pole upper radius at logarithmic input L.
Use ambient log(4B) at most log B+7/5 and additive root shift 213/20.
The value bounds both least pointwise witnesses and their full finite maximum. -/
noncomputable def eulerPrefixTwoPoleNeOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * ((500 / 821 : ℝ) * (L + 7 / 5) + 213 / 20) ^ 2

/-- For odd nonsquare n at most B under GRH and log B at least 500, an odd prime
with non-one Jacobi value lies below the common two-pole radius at B. Apply the
character theorem with ambient level 4B, including small input conductors, and
convert the value by quadratic reciprocity. No lower bound on log n is required. -/
theorem exists_odd_prime_ne_one_le_eulerPrefixTwoPole_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 500 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    LLS.exists_odd_prime_ne_one_le_twoPolePrincipalPrefix_even
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_isEven n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) (Nat.mul_le_mul_left 4 hnB) hGRH hLA
  have hlog : Real.log (4 * B : ℕ) ≤ Real.log B + 7 / 5 := by
    rw [LLS.log_original_quadratic_level hBpos]
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [he]
    linarith only [Real.log_two_lt_d9]
  have hr : 0 ≤ (500 / 821 : ℝ) * Real.log (4 * B : ℕ) + 213 / 20 := by linarith only [hLA]
  have hu :
    (500 / 821 : ℝ) * Real.log (4 * B : ℕ) + 213 / 20 ≤
      (500 / 821 : ℝ) * (Real.log B + 7 / 5) + 213 / 20 := by
    linarith only [hlog]
  have hs := mul_self_le_mul_self hr hu
  refine ⟨p, hp, ho, ?_, ?_⟩
  · dsimp only [eulerPrefixTwoPoleNeOneRadius]
    nlinarith only [hb, hs]
  · intro hj
    let : NeZero p := ⟨hp.ne_zero⟩
    have hg : (n : ℤ).gcd p = 1 := by
      by_contra h
      have hz := jacobiSym.eq_zero_iff_not_coprime.mpr h
      rw [hj] at hz
      exact one_ne_zero hz
    have hc : Nat.Coprime n p := by exact_mod_cast hg
    apply hv
    rw [NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp ho hc.symm, hj]
    exact Int.cast_one

/-- Under the same common-ambient assumptions, the least odd-prime non-one Jacobi
witness for n is bounded by the two-pole radius at B. Apply leastness to the
constructed prime. This is the input to the full finite-maximum theorem. -/
theorem primeNeOneWitness_cast_le_eulerPrefixTwoPole_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_ne_one_le_eulerPrefixTwoPole_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 500, QNeOne(B) is bounded by the affine two-pole
radius. Apply the common-ambient theorem to every admissible n at most B, including
small n. No finite-input certificate or separate small-range bound is needed. -/
theorem QNeOne_le_eulerPrefixTwoPole {B : ℕ} (hL : 500 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) := by
  apply QNeOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNeOneWitness_cast_le_eulerPrefixTwoPole_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- For real L at least 500, the odd non-one two-pole radius is strictly below L
squared. Bound its affine root by 1271L/2000 and compare rational squares.
This distinguishes the strict logarithmic-square improvement from applicability. -/
theorem eulerPrefixTwoPoleNeOneRadius_lt_log_square {L : ℝ} (hL : 500 ≤ L) :
    eulerPrefixTwoPoleNeOneRadius L < L ^ 2 := by
  have hr : 0 ≤ (500 / 821 : ℝ) * (L + 7 / 5) + 213 / 20 := by linarith only [hL]
  have hu : (500 / 821 : ℝ) * (L + 7 / 5) + 213 / 20 ≤ (1271 / 2000 : ℝ) * L := by
    linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [eulerPrefixTwoPoleNeOneRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 500, an odd prime non-one
Jacobi witness lies below the affine two-pole radius at n. Specialize the common
ambient endpoint to B=n. Character value zero remains an allowed witness. -/
theorem exists_prime_ne_one_witness_le_eulerPrefixTwoPole {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ eulerPrefixTwoPoleNeOneRadius (Real.log n) ∧ jacobiSym n p ≠ 1 := by
  exact exists_odd_prime_ne_one_le_eulerPrefixTwoPole_ambient hn hns le_rfl hGRH hL

/-- Under the same pointwise assumptions, bound the least odd-prime non-one Jacobi
witness by the affine two-pole radius. Specialize the common ambient leastness
interface. This is the pointwise companion of the full QNeOne bound. -/
theorem primeNeOneWitness_cast_le_eulerPrefixTwoPole {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ eulerPrefixTwoPoleNeOneRadius (Real.log n) := by
  exact primeNeOneWitness_cast_le_eulerPrefixTwoPole_ambient hn hns le_rfl hGRH hL hw

/-- For an odd nonsquare input n and a common ambient level A under GRH, the saved-gap
criterion with its structural exclusion and local costs yields an odd negative Jacobi prime.
Apply the even quadratic character and convert the unit-prime value by reciprocity.
This is a conditional interface, not a uniform numerical estimate for the exclusion budget. -/
theorem exists_odd_prime_neg_one_of_twoPolePrefixGap {n A : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hA : 4 * n ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 4 ≤ x) (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      let χ := NumberTheory.complexQuadraticCharacter n hn;
      AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor (4 * n) S
            (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
          ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        LLS.twoPoleConstantGap A (112 / 25) x + 2 * LLS.twoPoleEulerPrefixMass S) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff χ).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_of_twoPoleConstant_prefix χ
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hA hGRH hx hc S hS hgap
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  exact ⟨p, hp, hw.2.1, hb, hw.2.2⟩

/-- Under GRH, a common scale and prefix whose exclusion condition holds for every odd
nonsquare input up to B bound QNegOne(B) through the common cutoff. Apply the pointwise
negative-prime criterion and leastness at ambient level 4B.
The quantified exclusion hypothesis remains an explicit condition requiring a uniform proof. -/
theorem QNegOne_le_of_twoPolePrefixGap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      ∀ (n : ℕ) (hn : Odd n),
        ¬IsSquare n →
          n ≤ B →
            let χ := NumberTheory.complexQuadraticCharacter n hn;
            AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor (4 * n) S
                  (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4)
                    (3 / 4)) +
                ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
              LLS.twoPoleConstantGap (4 * B) (112 / 25) x + 2 * LLS.twoPoleEulerPrefixMass S) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply QNegOne_cast_le_of_forall (by linarith only [hx] : 0 ≤ (99 / 40 : ℝ) * x)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_of_twoPolePrefixGap ha.odd ha.not_isSquare
      (Nat.mul_le_mul_left 4 ha.le) hGRH hx S hS (hgap n ha.odd ha.not_isSquare ha.le)
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n _ ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, an odd nonsquare input with a common ambient level has a negative odd-prime
Jacobi witness whenever the joint principal gap pays the level-prime ramp cost. Use the full
Euler prefix through thirteen with saving one and the fixed conductor allocation. This is a
conditional smaller-scale interface; the numerical gap remains an explicit hypothesis. -/
theorem exists_odd_prime_neg_one_of_jointPrincipalGap {n A : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hA : 4 * n ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 25 ≤ x)
    (hgap :
      ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        LLS.jointRampPrincipalGap A (87 / 25) x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hcut : (13 : ℝ) ≤ (99 / 40 : ℝ) * x := by linarith only [hx]
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff χ).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  have hY : ∀ k ∈ Finset.Ioc 0 ⌊(13 : ℝ)⌋₊, (k : ℝ) ≤ (99 / 40 : ℝ) * x := by
    intro k hk
    norm_num only [Nat.floor_ofNat] at hk
    exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2).trans hcut
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_of_jointRampPrincipal_conductor_prefix χ
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hA hGRH
      (by linarith only [hx] : 2 ≤ x) (Y := 13) (by norm_num only) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      hY hc (g := 1)
      (by
        norm_num only [Nat.floor_ofNat]; exact LLS.twoPoleEulerPrefixMass_thirteen_saving_one)
      (by
        norm_num only at hgap ⊢; exact hgap)
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  exact ⟨p, hp, hw.2.1, hb, hw.2.2⟩

/-- If the joint-principal negative-gap condition holds for every admissible input through B,
the common cutoff bounds QNegOne(B). Apply the pointwise negative witness and leastness to each
input. This retains the uniform numerical obligation instead of treating a sampled gap as a
finite-maximum proof. -/
theorem QNegOne_le_of_jointPrincipalGap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 25 ≤ x)
    (hgap :
      ∀ n : ℕ,
        Odd n →
          ¬IsSquare n →
          n ≤ B →
          ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
            LLS.jointRampPrincipalGap (4 * B) (87 / 25) x) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (show 0 ≤ x by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_of_jointPrincipalGap ha.odd ha.not_isSquare
      (Nat.mul_le_mul_left 4 ha.le) hGRH hx (hgap n ha.odd ha.not_isSquare ha.le)
  exact
    (Nat.cast_le.mpr
          (NumberTheory.primeNegOneWitness_le n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
            ⟨hp, ho, hv⟩)).trans
      hb

end PseudoPrime.PseudoSquare
