/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.PartialCubicConductorBounds
public import PseudoPrime.LLS.PaperStatements.RationalPoleConductorRatios

/-! # Same-modulus envelopes from partial character families

These interfaces minimize the certified radii of selected character kernels and the full
annihilator family at one ambient modulus. Every radius keeps the ambient logarithmic
allowance. Fixed rational-pole coefficients and their comparisons belong to this LLS layer;
the module does not add dependencies to the common character or conductor foundations.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A quadratic conductor ratio of 23/50 beats the original index-four coefficient.
Input: none. Claim: a strict coefficient margin with exact rational data.
Proof: certified logarithm bounds and rational arithmetic.
Role: turn a single quadratic subfamily into a new Theorem 1.3 conductor region. -/
theorem quadratic_single_ratio_gap :
    (777 / 1000 : ℝ) * (23 / 50) ^ 2 <
      (1 / 4) * (1 - 1 / (4 : ℝ)) ^ 2 *
        (Real.log (2 * (4 : ℝ)) / (Real.log (2 * (4 : ℝ)) - 4)) ^ 2 := by
  have hid : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have he := Real.log_pow (2 : ℝ) 3
    norm_num only at he
    exact he
  norm_num only
  apply
    coefficient_lt_of_log_lower (l := (2079 / 1000 : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9]
  · norm_num only

/-- A selected quadratic conductor below ratio 23/50 attains the original index-four target.
Input: GRH, an order-two character and a target subgroup contained in its kernel.
Claim: the actual least outside prime obeys the original coefficient for all sufficiently
large ambient moduli, uniformly in the character and subgroup. The ambient logarithmic
allowance is chosen inside the strict margin; no scalar gap remains as an input. -/
theorem quadratic_single_theorem13 (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q),
              orderOf χ = 2 →
                H ≤ χ.toUnitHom.ker →
                Real.log χ.conductor ≤ (23 / 50 : ℝ) * Real.log q →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) <
                      ((1 / 4) * (1 - 1 / (4 : ℝ)) ^ 2 *
                          (Real.log (2 * (4 : ℝ)) / (Real.log (2 * (4 : ℝ)) - 4)) ^ 2) *
                        (Real.log q) ^ 2 :=
  Exists.elim
    (quadratic_partial_ratio_bound hg (r := (23 / 50 : ℝ)) (by norm_num only)
      quadratic_single_ratio_gap)
    fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq H χ ho hH hcost ↦
      hQ.2 q hq H χ χ ho ho hH hH ((min_self (Real.log χ.conductor)).symm ▸ hcost)⟩

/-- Two bounds for the same least element combine by taking their minimum.
Input: two actual least-prime certificates at one ambient target set.
Proof: uniqueness identifies the witnesses. Role: assemble the finite family envelope. -/
private theorem least_min_bound {s : Set ℕ} {A B : ℝ} (hA : ∃ p : ℕ, IsLeast s p ∧ (p : ℝ) ≤ A)
    (hB : ∃ p : ℕ, IsLeast s p ∧ (p : ℝ) ≤ B) : ∃ p : ℕ, IsLeast s p ∧ (p : ℝ) ≤ min A B :=
  Exists.elim hA fun p hp ↦
    Exists.elim hB fun _r hr ↦ ⟨p, hp.1, le_min hp.2 ((hp.1.unique hr.1).symm ▸ hr.2)⟩

/-- A quadratic subfamily and the full index-four family bound the same least outside prime.
Input: GRH, a positive ambient allowance, and a quadratic kernel containing the target.
Claim: the minimum of both certified squared radii is valid uniformly in the modulus.
Proof: intersect the two thresholds and use least-prime uniqueness.
Role: the cyclic index-four envelope, retaining the full-family alternative. -/
theorem quadratic_full_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q),
              H.index = 4 →
                orderOf χ = 2 →
                H ≤ χ.toUnitHom.ker →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) ≤
                      min ((Real.sqrt (777 / 1000) * Real.log χ.conductor + ε * Real.log q) ^ 2)
                        ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) * subgroupConductorLogSum H +
                            ε * Real.log q) ^
                          2) :=
  Exists.elim (quadratic_partial_min_radius hg hε) fun Q₂ h₂ ↦
    Exists.elim (rationalPole_index_four_conductor hg hε) fun Q₄ h₄ ↦
      ⟨max Q₂ Q₄, h₂.1.trans (le_max_left _ _), fun q _ hq H χ hi ho hH ↦
        least_min_bound
          (Exists.elim (h₂.2 q ((le_max_left _ _).trans hq) H χ χ ho ho hH hH) fun p hp ↦
            ⟨p, hp.1, hp.2.trans (min_le_left _ _)⟩)
          (h₄.2 q ((le_max_right _ _).trans hq) H hi)⟩

/-- Three quadratic subfamilies and the full index-four family give a four-way envelope.
Input: three order-two characters whose kernels contain an index-four subgroup.
Claim: one actual least outside prime lies below every displayed ambient-error radius.
Proof: combine the quadratic pair and the remaining quadratic/full-family bounds.
Role: handle all three nonprincipal characters of a biquadratic quotient, including the product. -/
theorem quadratic_triple_full_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ) (a b c : DirichletCharacter ℂ q),
              H.index = 4 →
                orderOf a = 2 →
                orderOf b = 2 →
                orderOf c = 2 →
                H ≤ a.toUnitHom.ker →
                H ≤ b.toUnitHom.ker →
                H ≤ c.toUnitHom.ker →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) ≤
                      min
                        (min ((Real.sqrt (777 / 1000) * Real.log a.conductor + ε * Real.log q) ^ 2)
                          ((Real.sqrt (777 / 1000) * Real.log b.conductor + ε * Real.log q) ^ 2))
                        (min ((Real.sqrt (777 / 1000) * Real.log c.conductor + ε * Real.log q) ^ 2)
                          ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) * subgroupConductorLogSum H +
                              ε * Real.log q) ^
                            2)) :=
  Exists.elim (quadratic_partial_min_radius hg hε) fun Q₂ h₂ ↦
    Exists.elim (quadratic_full_min_radius hg hε) fun Q₄ h₄ ↦
      ⟨max Q₂ Q₄, h₂.1.trans (le_max_left _ _), fun q _ hq H a b c hi ha hb hc hHa hHb hHc ↦
        least_min_bound (h₂.2 q ((le_max_left _ _).trans hq) H a b ha hb hHa hHb)
          (h₄.2 q ((le_max_right _ _).trans hq) H c hi hc hHc)⟩

/-- A witness outside a supergroup bounds the least eligible prime outside its subgroup.
Input: subgroup inclusion and a certified actual least outside prime for the supergroup.
Claim: the same real bound holds for an actual least outside prime of the smaller subgroup.
Proof: transfer membership and minimize the nonempty natural set.
Role: compare partial and full families at the same ambient modulus. -/
private theorem transfer_least_bound {q : ℕ} {H J : Subgroup (ZMod q)ˣ} {A : ℝ} (hHJ : H ≤ J)
    (hJ : ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q J) p ∧ (p : ℝ) ≤ A) :
    ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤ A :=
  letI : DecidablePred (fun r : ℕ ↦ r ∈ NumberTheory.primesOutside q H) := fun _ ↦
    Classical.propDecidable _
  Exists.elim hJ fun p hp ↦
    let hpH : p ∈ NumberTheory.primesOutside q H :=
      ⟨hp.1.1.1, hp.1.1.2.1, fun ⟨u, hu, he⟩ ↦ hp.1.1.2.2 ⟨u, hHJ hu, he⟩⟩
    let hn : ∃ r : ℕ, r ∈ NumberTheory.primesOutside q H := ⟨p, hpH⟩
    ⟨Nat.find hn, ⟨Nat.find_spec hn, fun _ hr ↦ Nat.find_min' hn hr⟩,
      (Nat.cast_le.mpr (Nat.find_min' hn hpH)).trans hp.2⟩

/-- Quadratic, cubic and full index-six families supply one same-modulus minimum.
Input: GRH and index-two/three supergroups of an index-six target subgroup.
Claim: its actual least outside prime satisfies all three certified squared radii with the
same positive ambient allowance. Proof: transfer partial witnesses and identify least elements.
Role: the cyclic index-six partial-family envelope without a supplied scalar gap. -/
theorem cubic_quadratic_full_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H J₂ J₃ : Subgroup (ZMod q)ˣ),
              H.index = 6 →
                J₂.index = 2 →
                J₃.index = 3 →
                H ≤ J₂ →
                H ≤ J₃ →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) ≤
                      min
                        ((Real.sqrt (777 / 1000) / ((2 : ℝ) - 1) * subgroupConductorLogSum J₂ +
                            ε * Real.log q) ^
                          2)
                        (min
                          ((Real.sqrt (7 / 10) / ((3 : ℝ) - 1) * subgroupConductorLogSum J₃ +
                              ε * Real.log q) ^
                            2)
                          ((Real.sqrt (549 / 1000) / ((6 : ℝ) - 1) * subgroupConductorLogSum H +
                              ε * Real.log q) ^
                            2)) :=
  Exists.elim (rationalPole_quadratic_conductor hg hε) fun Q₂ h₂ ↦
    Exists.elim (gamma_cubic_conductor hg hε) fun Q₃ h₃ ↦
      Exists.elim (rationalPole_index_six_conductor hg hε) fun Q₆ h₆ ↦
        ⟨max Q₂ (max Q₃ Q₆), h₂.1.trans (le_max_left _ _), fun q _ hq H J₂ J₃ hi hi₂ hi₃ hH₂ hH₃ ↦
          least_min_bound (transfer_least_bound hH₂ (h₂.2 q ((le_max_left _ _).trans hq) J₂ hi₂))
            (least_min_bound
              (transfer_least_bound hH₃
                (h₃.2 q ((le_max_left _ _).trans ((le_max_right _ _).trans hq)) J₃ hi₃))
              (h₆.2 q ((le_max_right _ _).trans ((le_max_right _ _).trans hq)) H hi))⟩

end PseudoPrime.LLS.PaperStatements
