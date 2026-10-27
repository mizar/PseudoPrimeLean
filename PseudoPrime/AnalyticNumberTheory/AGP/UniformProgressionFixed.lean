/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionTheta

/-! # Fixed-scale progression theta supply

The fixed-scale theta estimate needed by the AGP prime-supply construction,
stated separately from the all-`x` Proposition 1.5 count.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: fixed natural-number bounds `D` and `X₀`.

Claim: for every `X ≥ X₀`, there is a set `E` of at most `D` exceptional
moduli, each larger than `log(X^5)`, such that every coprime progression in
the AGP range has theta at least half its expected main term when its modulus
is not divisible by any member of `E`.

Content: the allowed moduli have the form `d*m`, where `m` is `1` or `4` and
`d ≤ X^2`; the residue is required to be coprime to the full modulus.

Role: this is the fixed-parameter consequence of paper95 Theorem 2.1 that
feeds the fifth-power prime-supply estimates. It does not assert the
zero-density or exceptional-modulus arguments that establish the supply.
-/
def AGPFixedThetaSupply : Prop :=
  ∃ (D X₀ : ℕ),
    ∀ X : ℕ,
      X₀ ≤ X →
        ∃ E : Finset ℕ,
          E.card ≤ D ∧
            (∀ e ∈ E, Real.log ((X ^ 5 : ℕ) : ℝ) < (e : ℝ)) ∧
            ∀ (m d r : ℕ),
              (m = 1 ∨ m = 4) →
                0 < d →
                d ≤ X ^ 2 →
                Nat.Coprime d m →
                1 < d * m →
                Nat.Coprime r (d * m) →
                (∀ e ∈ E, ¬e ∣ d * m) →
                (((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                  thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m) r

/--
Inputs: an `AGPFixedThetaSupply` and a scale above its fixed threshold.

Claim: the supplied exceptional set gives the exact theta lower bound for
progressions modulo `4*d` used by the fifth-power prime-set construction.

Proof: specialize the supply to `m = 4` and the CRT residue that is `1 mod d`
and `3 mod 4`; its coprimality follows from `progressionCoprimeResidue_spec`.

Role: exposes the fixed-scale analytic hypothesis in the form consumed by the
AGP progression-count endpoint.
-/
theorem agpFixedThetaSupply_four (hSupply : AGPFixedThetaSupply) :
    ∃ (D X₀ : ℕ),
      ∀ X : ℕ,
        X₀ ≤ X →
          ∃ E : Finset ℕ,
            E.card ≤ D ∧
              (∀ e ∈ E, Real.log ((X ^ 5 : ℕ) : ℝ) < (e : ℝ)) ∧
              ∀ d : ℕ,
                (hdm : Nat.Coprime d 4) →
                  0 < d →
                    d ≤ X ^ 2 →
                    (∀ e ∈ E, ¬e ∣ d * 4) →
                    (((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * 4) : ℝ))) ≤
                      thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
                        (progressionCoprimeResidue d 4 3 hdm) := by
  rcases hSupply with ⟨D, X₀, hSupply⟩
  refine ⟨D, X₀, ?_⟩
  intro X hX
  rcases hSupply X hX with ⟨E, hEcard, hElog, htheta⟩
  refine ⟨E, hEcard, hElog, ?_⟩
  intro d hdm hd hdX hAvoid
  have hdmOne : 1 < d * 4 := by
    have hmul : d < d * 4 := by
      calc
        d = d * 1 := by exact (Nat.mul_one d).symm
        _ < d * 4 := by
          simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (by norm_num only : 1 < 4) hd
    exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hd) hmul
  have hres := progressionCoprimeResidue_spec d 4 3 hdm (by norm_num only)
  exact
    htheta 4 d (progressionCoprimeResidue d 4 3 hdm) (Or.inr rfl) hd hdX hdm hdmOne hres.2.2 hAvoid

end PseudoPrime.AnalyticNumberTheory.AGP
