/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LowPrimeTightEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRecoveredOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRecoveredSeededOrder
public import PseudoPrime.Analysis.GaussianRecoveredRoot
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRecoveredBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularRefinedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeCutoff

/-! # Refined all-input witness envelope with total prime rounding -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the base and three analytic candidates at real logarithmic scale L,
combine exactly the certified domains, using the base outside each domain.
The two triangular candidates are guarded at their respective logarithmic entrances. -/
noncomputable def refinedGuardMin (L B G R S : ℝ) : ℝ :=
  min B <|
    min (if 63 ≤ L then G else B) <|
    min (if 101 ≤ L then R else B) <|
    min (if 63 ≤ L then S else B) <|
    min (if 1100000000000 ≤ L then (71 / 250) * L ^ 2 else B)
      (if 2000000000000 ≤ L then (28237 / 100000) * L ^ 2 else B)

/-- Select the valid analytic candidates on each ordered logarithmic interval.
The inputs are the same base and three candidate values as the guarded minimum;
only inactive and repeated base values are removed. -/
noncomputable def refinedGuardSelected (L B G R S : ℝ) : ℝ :=
  if L < 63 then B
  else
    if L < 101 then min B (min G S)
    else
      if L < 1100000000000 then min B (min G (min R S))
      else
        if L < 2000000000000 then min B (min G (min R (min S ((71 / 250) * L ^ 2))))
        else min B (min G (min R (min S (min ((71 / 250) * L ^ 2) ((28237 / 100000) * L ^ 2)))))

/-- For every real scale and every candidate value, the ordered selection equals
the guarded minimum. Split at the certified entrances and remove duplicate minima.
No arithmetic, primality, or analytic assumption enters this algebraic identity. -/
theorem refinedGuardMin_eq_selected (L B G R S : ℝ) :
    refinedGuardMin L B G R S = refinedGuardSelected L B G R S := by
  by_cases h63 : L < 63
  · have h101 : ¬101 ≤ L := by linarith only [h63]
    have he : ¬1100000000000 ≤ L := by linarith only [h63]
    have ht : ¬2000000000000 ≤ L := by linarith only [h63]
    simp only [refinedGuardMin, refinedGuardSelected, ite_eq_left h63,
      ite_eq_right (not_le.mpr h63), ite_eq_right h101, ite_eq_right he, ite_eq_right ht, min_self]
  · have hg : 63 ≤ L := le_of_not_gt h63
    by_cases h101 : L < 101
    · have he : ¬1100000000000 ≤ L := by linarith only [h101]
      have ht : ¬2000000000000 ≤ L := by linarith only [h101]
      simp only [refinedGuardMin, refinedGuardSelected, ite_eq_right h63, ite_eq_left hg,
        ite_eq_left h101, ite_eq_right (not_le.mpr h101), ite_eq_right he, ite_eq_right ht,
        min_self]
      rw [min_left_comm G B (min S B), ← min_assoc B B _, min_self]
      rw [min_comm S B, min_left_comm G B S, ← min_assoc B B _, min_self]
    · have hr : 101 ≤ L := le_of_not_gt h101
      by_cases he : L < 1100000000000
      · have ht : ¬2000000000000 ≤ L := by linarith only [he]
        simp only [refinedGuardMin, refinedGuardSelected, ite_eq_right h63, ite_eq_right h101,
          ite_eq_left hg, ite_eq_left hr, ite_eq_left he, ite_eq_right (not_le.mpr he),
          ite_eq_right ht, min_self]
        rw [min_comm S B, min_left_comm R B S, min_left_comm G B (min R S), ← min_assoc B B _,
          min_self]
      · have he' : 1100000000000 ≤ L := le_of_not_gt he
        by_cases ht : L < 2000000000000
        · simp only [refinedGuardMin, refinedGuardSelected, ite_eq_right h63, ite_eq_right h101,
            ite_eq_right he, ite_eq_left hg, ite_eq_left hr, ite_eq_left he', ite_eq_left ht,
            ite_eq_right (not_le.mpr ht)]
          rw [min_comm ((71 / 250) * L ^ 2) B, min_left_comm S B ((71 / 250) * L ^ 2),
            min_left_comm R B (min S ((71 / 250) * L ^ 2)),
            min_left_comm G B (min R (min S ((71 / 250) * L ^ 2))), ← min_assoc B B _, min_self]
        · simp only [refinedGuardMin, refinedGuardSelected, ite_eq_right h63, ite_eq_right h101,
            ite_eq_right he, ite_eq_right ht, ite_eq_left hg, ite_eq_left hr, ite_eq_left he',
            ite_eq_left (le_of_not_gt ht)]

/-- For natural input n, intersect the extended low-prime envelope with the
recovered Gaussian, fixed-stencil Gamma, seeded Gaussian, and triangular bounds.
Each candidate is used only in its proved logarithmic domain. This is the
unrounded public analytic cutoff for actual and least prime MR witnesses. -/
noncomputable def refinedWitnessEnvelope (n : ℕ) : ℝ :=
  refinedGuardMin (Real.log n) (lowPrimeTightEnvelope n)
    (Analysis.gaussianRecoveredBound (Real.log n)) (gammaRecoveredBound (Real.log n))
    (Analysis.gaussianRecoveredSeeded (Real.log n))

/-- The interval form of the refined analytic envelope, using the nine extended
low-prime steps and the baseline selection as the base. The five larger-scale
regions retain exactly the certified candidates, with their original guards. -/
noncomputable def refinedSelectedEnvelope (n : ℕ) : ℝ :=
  refinedGuardSelected (Real.log n) (lowPrimeTightSelected n)
    (Analysis.gaussianRecoveredBound (Real.log n)) (gammaRecoveredBound (Real.log n))
    (Analysis.gaussianRecoveredSeeded (Real.log n))

/-- Round the refined analytic cutoff to its greatest admissible prime.
The total prime-rounding function retains two and does not enlarge any real cutoff;
actual rejecting-prime witnesses are preserved. -/
noncomputable def refinedPrimeEnvelope (n : ℕ) : ℝ :=
  primeRound (refinedWitnessEnvelope n)

/-- For every natural input, the refined analytic cutoff is at most its extended
low-prime base. This immediate minimum projection feeds baseline non-worsening. -/
theorem refinedWitnessEnvelope_le_low (n : ℕ) :
    refinedWitnessEnvelope n ≤ lowPrimeTightEnvelope n := by exact min_le_left _ _

/-- For every natural input, the refined analytic cutoff is at most the fixed
baseline next envelope. Compose the minimum projection with the low-prime bound;
no GRH or compositeness hypothesis is needed for numerical non-worsening. -/
theorem refinedWitnessEnvelope_le_next (n : ℕ) :
    refinedWitnessEnvelope n ≤ nextWitnessEnvelope n := by
  exact (refinedWitnessEnvelope_le_low n).trans (lowPrimeTightEnvelope_le_next n)

/-- For every natural input, rounding does not enlarge the analytic cutoff.
Apply the total real-cutoff rounding inequality to preserve numerical non-worsening. -/
theorem refinedPrimeEnvelope_le_refined (n : ℕ) :
    refinedPrimeEnvelope n ≤ refinedWitnessEnvelope n := by exact primeRound_le _

/-- For every natural input greater than one, the guarded and interval forms
of the refined envelope agree. Rewrite the extended low-prime selection and
apply the purely algebraic guard identity; this does not assume GRH or primality. -/
theorem refined_eq_selected {n : ℕ} (hn : 1 < n) :
    refinedWitnessEnvelope n = refinedSelectedEnvelope n := by
  simp only [refinedWitnessEnvelope, refinedSelectedEnvelope, lowPrimeTight_eq_selected hn,
    refinedGuardMin_eq_selected]

/-- A common lower bound for the extended low-prime base and every valid new
candidate also bounds the refined envelope. Resolve each guard with the base
as fallback, then combine the inequalities by minimum. -/
theorem refined_lower_of_candidates {n : ℕ} {C : ℝ} (hB : C ≤ lowPrimeTightEnvelope n)
    (hG : 63 ≤ Real.log n → C ≤ Analysis.gaussianRecoveredBound (Real.log n))
    (hR : 101 ≤ Real.log n → C ≤ gammaRecoveredBound (Real.log n))
    (hS : 63 ≤ Real.log n → C ≤ Analysis.gaussianRecoveredSeeded (Real.log n))
    (hE : 1100000000000 ≤ Real.log n → C ≤ (71 / 250) * Real.log n ^ 2)
    (hT : 2000000000000 ≤ Real.log n → C ≤ (28237 / 100000) * Real.log n ^ 2) :
    C ≤ refinedWitnessEnvelope n := by
  have guard {Q : Prop} [Decidable Q] {v : ℝ} (h : Q → C ≤ v) :
    C ≤ if Q then v else lowPrimeTightEnvelope n := by
    by_cases hq : Q
    · rw [ite_eq_left hq]
      exact h hq
    · rw [ite_eq_right hq]
      exact hB
  exact
    le_min hB
      (le_min (guard hG) (le_min (guard hR) (le_min (guard hS) (le_min (guard hE) (guard hT)))))

/-- On its certified domain, the refined envelope is no larger than the
single-root Gaussian candidate. Project from the guarded minimum and resolve
the active guard; this is a numerical inequality without GRH assumptions. -/
theorem refined_le_gaussian {n : ℕ} (hL : (63 : ℝ) ≤ Real.log n) :
    refinedWitnessEnvelope n ≤ Analysis.gaussianRecoveredBound (Real.log n) := by
  have h :
    refinedWitnessEnvelope n ≤
      (if 63 ≤ Real.log n then Analysis.gaussianRecoveredBound (Real.log n)
      else lowPrimeTightEnvelope n) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  simpa only [ite_eq_left hL] using h

/-- On its certified domain, the refined envelope is no larger than the
fixed-stencil Gamma candidate. Project from the guarded minimum and resolve
the active guard; this is a numerical inequality without GRH assumptions. -/
theorem refined_le_gamma {n : ℕ} (hL : (101 : ℝ) ≤ Real.log n) :
    refinedWitnessEnvelope n ≤ gammaRecoveredBound (Real.log n) := by
  have h :
    refinedWitnessEnvelope n ≤
      (if 101 ≤ Real.log n then gammaRecoveredBound (Real.log n) else lowPrimeTightEnvelope n) := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  simpa only [ite_eq_left hL] using h

/-- On its certified domain, the refined envelope is no larger than the
recovered seeded Gaussian candidate. Project from the guarded minimum and resolve
the active guard; this is a numerical inequality without GRH assumptions. -/
theorem refined_le_seeded {n : ℕ} (hL : (63 : ℝ) ≤ Real.log n) :
    refinedWitnessEnvelope n ≤ Analysis.gaussianRecoveredSeeded (Real.log n) := by
  have h :
    refinedWitnessEnvelope n ≤
      (if 63 ≤ Real.log n then Analysis.gaussianRecoveredSeeded (Real.log n)
      else lowPrimeTightEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  simpa only [ite_eq_left hL] using h

/-- On its certified domain, the refined envelope is no larger than the
earlier triangular candidate. Project from the guarded minimum and resolve
the active guard; this is a numerical inequality without GRH assumptions. -/
theorem refined_le_earlier {n : ℕ} (hL : (1100000000000 : ℝ) ≤ Real.log n) :
    refinedWitnessEnvelope n ≤ (71 / 250) * Real.log n ^ 2 := by
  have h :
    refinedWitnessEnvelope n ≤
      (if 1100000000000 ≤ Real.log n then (71 / 250) * Real.log n ^ 2
      else lowPrimeTightEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  simpa only [ite_eq_left hL] using h

/-- On its certified domain, the refined envelope is no larger than the
sharper triangular candidate. Project from the guarded minimum and resolve
the active guard; this is a numerical inequality without GRH assumptions. -/
theorem refined_le_triangular {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    refinedWitnessEnvelope n ≤ (28237 / 100000) * Real.log n ^ 2 := by
  have h :
    refinedWitnessEnvelope n ≤
      (if 2000000000000 ≤ Real.log n then (28237 / 100000) * Real.log n ^ 2
      else lowPrimeTightEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  simpa only [ite_eq_left hL] using h

/-- Under GRH, every odd composite greater than one has a least rejecting prime
below every valid refined candidate. Transfer each actual witness bound to
one least witness, then apply the guarded-minimum lower-bound interface. -/
theorem exists_least_refinedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ refinedWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_lowPrimeTightEnvelope hn ho hc hGRH
  have transfer {C : ℝ}
    (hw : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := hw
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  refine ⟨p, hp, hr, refined_lower_of_candidates hb ?_ ?_ ?_ ?_ ?_, hm⟩
  · intro h; exact transfer (exists_prime_gaussianRecovered ho hc hGRH h)
  · intro h; exact transfer (exists_prime_gammaRecovered hn ho hc hGRH h)
  · intro h; exact transfer (exists_prime_recoveredSeededSelected ho hc hGRH h)
  · intro h; exact transfer (exists_prime_triangularEarlier hn ho hc hGRH h)
  · intro h; exact transfer (exists_prime_triangularRefined hn ho hc hGRH h)

/-- Under GRH, every odd composite greater than one has an actual rejecting
prime below the refined analytic envelope. Forget leastness from the common
witness theorem; no factorization or subgroup condition remains. -/
theorem exists_prime_refinedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_refinedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Under the all-input GRH assumptions, the common least rejecting prime
remains below the prime-rounded envelope. Prime-preserving rounding transfers
the numerical bound without changing the witness or its minimality. -/
theorem exists_least_refinedPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ refinedPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_refinedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Under GRH, every odd composite greater than one has a rejecting prime
below the rounded envelope. Extract it from the rounded least-witness theorem. -/
theorem exists_prime_refinedPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPrimeEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_refinedPrimeEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Under the all-input GRH assumptions, the interval selection bounds an
actual rejecting prime. Rewrite the numerical guarded/selected identity and
apply the refined analytic witness theorem. -/
theorem exists_prime_refinedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedSelectedEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← refined_eq_selected hn]
  exact exists_prime_refinedEnvelope hn ho hc hGRH

/-- Under the all-input GRH assumptions, the interval selection bounds the
least rejecting prime. The numerical selection identity transfers both the
analytic bound and the unchanged leastness property. -/
theorem exists_least_refinedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ refinedSelectedEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← refined_eq_selected hn]
  exact exists_least_refinedEnvelope hn ho hc hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
