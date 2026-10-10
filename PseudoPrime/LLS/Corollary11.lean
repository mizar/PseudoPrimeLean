/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.LLS.Corollary11SmallBounds
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Least quadratic nonresidues for LLS Corollary 1.1. -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A nontrivial character has a prime strictly below the logarithmic-square cutoff
under GRH at level at least 3000. The strict cutoff follows from the existing
counterexample exclusion, without a transcendence argument at the endpoint. -/
theorem exists_prime_not_one_lt_log_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) < (Real.log q) ^ 2 ∧ χ p ≠ 1 :=
  Classical.not_not.mp
    (fun h ↦
      not_characterTrivialBelow_log_sq χ hne hq hGRH
        (fun p hp hpx ↦ Classical.byContradiction (fun hn ↦ h ⟨p, hp, hpx, hn⟩)))

/-- A positive nonsquare witness below a real cutoff gives the same strict bound
for the least positive nonsquare. Natural well-ordering supplies minimality. -/
theorem exists_least_positive_nonsquare_lt {q : ℕ} {x : ℝ}
    (h : ∃ n : ℕ, 0 < n ∧ ¬IsSquare (n : ZMod q) ∧ (n : ℝ) < x) :
    ∃ n : ℕ, IsLeast {m : ℕ | 0 < m ∧ ¬IsSquare (m : ZMod q)} n ∧ (n : ℝ) < x :=
  letI : DecidablePred (fun n : ℕ ↦ 0 < n ∧ ¬IsSquare (n : ZMod q)) := Classical.decPred _
  let hex : ∃ n : ℕ, 0 < n ∧ ¬IsSquare (n : ZMod q) := Exists.elim h (fun n hn ↦ ⟨n, hn.1, hn.2.1⟩)
  ⟨Nat.find hex, ⟨Nat.find_spec hex, fun _m hm ↦ Nat.find_min' hex hm⟩,
    Exists.elim h
      (fun _m hm ↦ lt_of_le_of_lt (Nat.cast_le.mpr (Nat.find_min' hex ⟨hm.1, hm.2.1⟩)) hm.2.2)⟩

/-- For a prime modulus between 5 and 2999, the least positive quadratic nonresidue
is strictly below the logarithmic square. The finite witness and natural minimality
give this bounded part of Corollary 1.1 without an analytic hypothesis. -/
theorem exists_least_positive_nonsquare_lt_log_sq_small {q : ℕ} (hp : q.Prime) (h5 : 5 ≤ q)
    (hq : q < 3000) :
    ∃ n : ℕ, IsLeast {m : ℕ | 0 < m ∧ ¬IsSquare (m : ZMod q)} n ∧ (n : ℝ) < (Real.log q) ^ 2 :=
  exists_least_positive_nonsquare_lt (exists_positive_nonsquare_lt_log_sq_small hp h5 hq)

/-- For a real `x > 1`, prove `log x < sqrt x` by applying the strict logarithm
bound to the fourth root, rewriting its logarithm, and using a square inequality.
This gives the logarithmic-square cutoff needed to keep a prime witness below its modulus. -/
theorem log_lt_sqrt_of_one_lt {x : ℝ} (hx : 1 < x) : Real.log x < Real.sqrt x := by
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hs : 1 < Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hx
  have ht : 1 < Real.sqrt (Real.sqrt x) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hs
  have hl := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one ht) (ne_of_gt ht)
  have hlog := Real.log_sqrt (Real.sqrt_nonneg x)
  have hlogx := Real.log_sqrt hx0
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg x)
  nlinarith only [hl, hlog, hlogx, hsq, sq_nonneg (Real.sqrt (Real.sqrt x) - 2)]

/-- For a real `x > 1`, the positive logarithm and `log x < sqrt x` imply
`(log x)² < x`. Squaring is justified by positivity and the square-root identity.
This ensures a witness below the logarithmic-square cutoff is nonzero modulo `x`
when `x` is a prime natural modulus. -/
theorem log_sq_lt_of_one_lt {x : ℝ} (hx : 1 < x) : (Real.log x) ^ 2 < x := by
  have hl := log_lt_sqrt_of_one_lt hx
  have hp := Real.log_pos hx
  have hs := Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one hx))
  nlinarith only [hl, hp, hs, Real.sqrt_nonneg x]

/-- For a prime modulus `q ≥ 3000`, GRH supplies a positive nonsquare strictly
below `(log q)²`. Apply the strict character bound to the nontrivial quadratic character.
The logarithmic-square bound places its prime witness below `q`, so its residue is
nonzero; a square residue would make the character value one. This proves the large
modulus case of Corollary 1.1 before taking the least positive nonsquare. -/
theorem exists_positive_nonsquare_lt_log_sq_large {q : ℕ} (hp : q.Prime) (hq : 3000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ n : ℕ, 0 < n ∧ ¬IsSquare (n : ZMod q) ∧ (n : ℝ) < (Real.log q) ^ 2 := by
  let : Fact q.Prime := ⟨hp⟩
  let : NeZero q := ⟨hp.ne_zero⟩
  let χ : DirichletCharacter ℂ q := (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)
  have hq2 : q ≠ 2 := ne_of_gt (lt_of_lt_of_le (of_decide_eq_true rfl : 2 < 3000) hq)
  have hc : ringChar (ZMod q) ≠ 2 := (ZMod.ringChar_zmod_n q).symm ▸ hq2
  have hχ : χ ≠ 1 :=
    MulChar.ringHomComp_ne_one_iff Int.cast_injective |>.mpr (quadraticChar_ne_one hc)
  obtain ⟨p, hp', hplog, hχp⟩ := exists_prime_not_one_lt_log_sq χ hχ hq hGRH
  have hq1 : (1 : ℝ) < q := Nat.one_lt_cast.mpr hp.one_lt
  have hpq : p < q := Nat.cast_lt.mp (hplog.trans (log_sq_lt_of_one_lt hq1))
  have hp0 : (p : ZMod q) ≠ 0 := fun h ↦
    (Nat.not_dvd_of_pos_of_lt hp'.pos hpq) ((ZMod.natCast_eq_zero_iff p q).mp h)
  refine ⟨p, hp'.pos, ?_, hplog⟩
  intro hs
  apply hχp
  change (Int.castRingHom ℂ) (quadraticChar (ZMod q) (p : ZMod q)) = 1
  rw [(quadraticChar_one_iff_isSquare hp0).mpr hs, map_one]

end PseudoPrime.LLS
