/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.PartialCharacterBounds
public import PseudoPrime.NumberTheory.CrtCharacters
public import PseudoPrime.NumberTheory.QuadraticCrtKernels

/-! # Partial quadratic subgroup bounds retaining conductor savings -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- If H is contained in J, every eligible prime outside J is outside H.
Keep primality and exclusion of modulus divisors and transfer the failed
residue membership through the subgroup inclusion. -/
private theorem primesOutside_of_subgroup_le {q p : ℕ} {H J : Subgroup (ZMod q)ˣ} (hHJ : H ≤ J)
    (hp : p ∈ NumberTheory.primesOutside q J) : p ∈ NumberTheory.primesOutside q H := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  rintro ⟨u, hu, hup⟩
  exact hp.2.2 ⟨u, hHJ hu, hup⟩

/-- An actual prime outside a larger subgroup J supplies an actual least
prime outside H, no larger than the supplied prime. Use the natural least
element of the nonempty eligible-prime set after the inclusion transfer. -/
private theorem leastOutside_of_subgroup_le {q p : ℕ} {H J : Subgroup (ZMod q)ˣ} (hHJ : H ≤ J)
    (hp : p ∈ NumberTheory.primesOutside q J) :
    ∃ r : ℕ, IsLeast (NumberTheory.primesOutside q H) r ∧ r ≤ p := by
  classical
  have hex : ∃ r : ℕ, r ∈ NumberTheory.primesOutside q H := ⟨p, primesOutside_of_subgroup_le hHJ hp⟩
  exact
    ⟨Nat.find hex, ⟨Nat.find_spec hex, fun _ hr ↦ Nat.find_min' hex hr⟩,
      Nat.find_min' hex (primesOutside_of_subgroup_le hHJ hp)⟩

/-- Under GRH, an index-two subgroup with conductor-log sum at most half
log q gives a strict 39/200 log(q)^2 bound for the actual least prime outside
any contained subgroup H. Choose the ambient allowance uniformly before
applying the rational-pole certificate; excluded modulus primes are retained. -/
theorem quadratic_half_conductor_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ J H : Subgroup (ZMod q)ˣ,
              J.index = 2 →
                H ≤ J →
                subgroupConductorLogSum J ≤ Real.log q / 2 →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) < (39 / 200 : ℝ) * Real.log q ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ :=
    least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 2)
      (by norm_num only : (0 : ℝ) < 777 / 1000) (by norm_num only : (0 : ℝ) ≤ 1 / 2)
      (by norm_num only : (777 / 1000 : ℝ) * (1 / 2) ^ 2 < 39 / 200)
      (fun _ hε ↦ rationalPole_quadratic_conductor hg hε)
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq J H hi hHJ hsum
  have hs : subgroupConductorLogSum J ≤ (1 / 2 : ℝ) * ((2 : ℝ) - 1) * Real.log q := by
    nlinarith only [hsum]
  obtain ⟨p, hp, hpb⟩ := hb q hq J hi hs
  obtain ⟨r, hr, hrp⟩ := leastOutside_of_subgroup_le hHJ hp.1
  exact ⟨r, hr, (Nat.cast_le.mpr hrp).trans_lt hpb⟩

/-- Under GRH, two index-two supergroups whose conductor-log sums total at
most log q supply a strict 39/200 log(q)^2 least-outside-prime bound for
any common subgroup H, uniformly for sufficiently large q.
At least one of the two supergroups has the required half-log conductor budget. -/
theorem quadratic_pair_conductor_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ J₁ J₂ H : Subgroup (ZMod q)ˣ,
              J₁.index = 2 →
                J₂.index = 2 →
                H ≤ J₁ →
                H ≤ J₂ →
                subgroupConductorLogSum J₁ + subgroupConductorLogSum J₂ ≤ Real.log q →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) < (39 / 200 : ℝ) * Real.log q ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ := quadratic_half_conductor_bound hg
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq J₁ J₂ H hi₁ hi₂ hH₁ hH₂ hsum
  by_cases h₁ : subgroupConductorLogSum J₁ ≤ Real.log q / 2
  · exact hb q hq J₁ H hi₁ hH₁ h₁
  · exact hb q hq J₂ H hi₂ hH₂ (by linarith only [hsum, h₁])

/-- For positive log scale L and full index-four conductor sum at least 2L,
the partial quadratic coefficient 39/200 beats the full 623/1000 radius,
even with any nonnegative ambient allowance. Square nonnegative expressions
and use the strict rational coefficient gap. This does not prove the original
unrestricted index-four target coefficient. -/
theorem quadratic_pair_strict_gain {L S η : ℝ} (hL : 0 < L) (hS : 2 * L ≤ S) (hη : 0 ≤ η) :
    (39 / 200 : ℝ) * L ^ 2 < (Real.sqrt (623 / 1000) / 3 * S + η * L) ^ 2 := by
  have hpos : 0 ≤ S := (mul_pos (by norm_num only : (0 : ℝ) < 2) hL).le.trans hS
  have hm := mul_self_le_mul_self (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hL.le) hS
  have hr : 0 ≤ Real.sqrt (623 / 1000) / 3 * S :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num only)) hpos
  have he : 0 ≤ η * L := mul_nonneg hη hL.le
  have hs := mul_self_le_mul_self hr (le_add_of_nonneg_right he)
  have hid : (Real.sqrt (623 / 1000) / 3 * S) ^ 2 = (623 / 9000 : ℝ) * S ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 623 / 1000)]
    ring
  have hsq : 0 < L ^ 2 := sq_pos_of_pos hL
  nlinarith only [hm, hs, hid, hsq]

/-- Under GRH, two quadratic characters on nonzero component levels give
a uniform strict 39/200 log(m*n)^2 bound outside the intersection of their
lifted unit kernels. Change of level preserves order and conductor, and each
component conductor divides its level. No coprimality or cyclic quotient is
needed for this bound; the modulus-divisor exclusion stays at the ambient level. -/
theorem quadratic_crt_pair_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (m n : ℕ) [NeZero m] [NeZero n],
          Q ≤ m * n →
            ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
              orderOf α = 2 →
                orderOf β = 2 →
                ∃ p : ℕ,
                  IsLeast
                      (NumberTheory.primesOutside (m * n)
                        ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
                          (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom.ker))
                      p ∧
                    (p : ℝ) < (39 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ := quadratic_pair_conductor_bound hg
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hmn α β hα hβ
  let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
  let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
  have ha : orderOf a = 2 :=
    (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
          (DirichletCharacter.changeLevel_injective _) α).trans
      hα
  have hb' : orderOf b = 2 :=
    (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
          (DirichletCharacter.changeLevel_injective _) β).trans
      hβ
  apply
    hb (m * n) hmn a.toUnitHom.ker b.toUnitHom.ker _
      ((NumberTheory.index_kernel_eq_order a).trans ha)
      ((NumberTheory.index_kernel_eq_order b).trans hb') inf_le_left inf_le_right
  rw [quadratic_kernel_conductor_sum a ha, quadratic_kernel_conductor_sum b hb']
  have hca : a.conductor = α.conductor := DirichletCharacter.conductor_changeLevel α _
  have hcb : b.conductor = β.conductor := DirichletCharacter.conductor_changeLevel β _
  rw [hca, hcb, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  exact
    add_le_add
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero α.conductor_ne_zero))
        (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) α.conductor_dvd_level)))
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero β.conductor_ne_zero))
        (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) β.conductor_dvd_level)))

/-- Three distinct annihilator characters a, b and a*b give a lower bound
for the full conductor-log sum. Embed this three-element set into the full
annihilator and retain nonnegative omitted conductor logarithms. -/
theorem conductor_sum_ge_three {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a b : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (ha : a ≠ a * b) (hb : b ≠ a * b) :
    Real.log a.val.conductor + Real.log b.val.conductor + Real.log (a * b).val.conductor ≤
      subgroupConductorLogSum H := by
  classical
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (show ({a, b, a * b} : Finset (NumberTheory.subgroupAnnihilator H)) ⊆ Finset.univ from
        Finset.subset_univ _)
      (fun ψ _ _ ↦ Real.log_natCast_nonneg ψ.val.conductor)
  have hae : a ∉ ({b, a * b} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  rw [Finset.sum_insert hae, Finset.sum_insert (by simpa only [Finset.mem_singleton] using hb),
    Finset.sum_singleton] at ht
  rw [subgroupConductorLogSum, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Subgroup.coe_one, DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one,
    sub_zero]
  linarith only [ht]

/-- For primitive characters at coprime component levels greater than one,
the full conductor-log sum of the intersection of their lifted kernels is at
least twice log(m*n). The two lifted characters and their product are distinct
and have conductors m, n and m*n. This identifies a concrete region where
partial annihilator subgroups can improve the full average. -/
theorem crt_kernel_inf_cost_lower {m n : ℕ} [NeZero m] [NeZero n] (α : DirichletCharacter ℂ m)
    (β : DirichletCharacter ℂ n) (ha : α.IsPrimitive) (hb : β.IsPrimitive) (hmn : Nat.Coprime m n)
    (hm : 1 < m) (hn : 1 < n) :
    2 * Real.log (m * n : ℕ) ≤
      subgroupConductorLogSum
        ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
          (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom.ker) := by
  classical
  let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
  let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
  let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
  have hca : a.conductor = m := (DirichletCharacter.conductor_changeLevel α _).trans ha
  have hcb : b.conductor = n := (DirichletCharacter.conductor_changeLevel β _).trans hb
  have hc : (a * b).conductor = m * n := by
    rw [NumberTheory.conductor_mul_of_coprime a b (by simpa only [hca, hcb] using hmn), hca, hcb]
  have hmem (χ : DirichletCharacter ℂ (m * n)) (hH : H ≤ χ.toUnitHom.ker) :
    χ ∈ NumberTheory.subgroupAnnihilator H := by
    apply (NumberTheory.mem_subgroupAnnihilator_iff H χ).mpr
    intro u hu
    have he := congrArg Units.val (MonoidHom.mem_ker.mp (hH hu))
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using he
  let A : NumberTheory.subgroupAnnihilator H := ⟨a, hmem a inf_le_left⟩
  let B : NumberTheory.subgroupAnnihilator H := ⟨b, hmem b inf_le_right⟩
  have hAB : A ≠ B := by
    intro he
    have hec := congrArg (fun ψ : NumberTheory.subgroupAnnihilator H ↦ ψ.val.conductor) he
    change a.conductor = b.conductor at hec
    rw [hca, hcb] at hec
    have hg := hmn.gcd_eq_one
    rw [hec, Nat.gcd_self] at hg
    exact (Nat.ne_of_gt hn) hg
  have hA : A ≠ A * B := by
    intro he
    have hec := congrArg (fun ψ : NumberTheory.subgroupAnnihilator H ↦ ψ.val.conductor) he
    change a.conductor = (a * b).conductor at hec
    rw [hca, hc] at hec
    nlinarith only [hec, hm, hn]
  have hB : B ≠ A * B := by
    intro he
    have hec := congrArg (fun ψ : NumberTheory.subgroupAnnihilator H ↦ ψ.val.conductor) he
    change b.conductor = (a * b).conductor at hec
    rw [hcb, hc] at hec
    nlinarith only [hec, hm, hn]
  have ht := conductor_sum_ge_three H A B hAB hA hB
  change Real.log a.conductor + Real.log b.conductor + Real.log (a * b).conductor ≤ _ at ht
  rw [hca, hcb, hc, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))] at ht
  change 2 * Real.log (m * n : ℕ) ≤ subgroupConductorLogSum H
  rw [Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  linarith only [ht]

/-- Under GRH, primitive quadratic characters at coprime component levels
give an actual least outside prime below 39/200 log(m*n)^2, strictly smaller
than the full index-four rational-pole main radius. Supply the proved full
conductor lower bound, so no unverified conductor region remains an input.
This comparison does not assert the unrestricted original Theorem 1.3 coefficient. -/
theorem quadratic_crt_strict_full_gain
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (m n : ℕ) [NeZero m] [NeZero n],
          Nat.Coprime m n →
            1 < m →
            1 < n →
            Q ≤ m * n →
            ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
              orderOf α = 2 →
                orderOf β = 2 →
                α.IsPrimitive →
                β.IsPrimitive →
                ∃ p : ℕ,
                  IsLeast
                      (NumberTheory.primesOutside (m * n)
                        ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
                          (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom.ker))
                      p ∧
                    (p : ℝ) < (39 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 ∧
                    (39 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 <
                      (Real.sqrt (623 / 1000) / 3 *
                          subgroupConductorLogSum
                            ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n)
                                  α).toUnitHom.ker ⊓
                              (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m)
                                  β).toUnitHom.ker)) ^
                        2 := by
  obtain ⟨Q, hQ, hbound⟩ := quadratic_crt_pair_bound hg
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hmn hm hn hq α β hα hβ ha hb
  obtain ⟨p, hp, hpb⟩ := hbound m n hq α β hα hβ
  have hL : 0 < Real.log (m * n : ℕ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by nlinarith only [hm, hn]))
  have hc := crt_kernel_inf_cost_lower α β ha hb hmn hm hn
  have hs := quadratic_pair_strict_gain hL hc (le_refl (0 : ℝ))
  exact ⟨p, hp, hpb, by simpa only [zero_mul, add_zero] using hs⟩

/-- For primitive quadratic characters at coprime component levels, retain
both the actual index-four common kernel and its strict partial-family
least-prime improvement over the full rational-pole main radius.
Supply the proved kernel index to the existing analytic comparison. -/
theorem quadratic_crt_index_four_gain (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (m n : ℕ) [NeZero m] [NeZero n],
          Nat.Coprime m n →
            1 < m →
            1 < n →
            Q ≤ m * n →
            ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
              orderOf α = 2 →
                orderOf β = 2 →
                α.IsPrimitive →
                β.IsPrimitive →
                ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
                        (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m)
                            β).toUnitHom.ker).index =
                    4 ∧
                  ∃ p : ℕ,
                    IsLeast
                        (NumberTheory.primesOutside (m * n)
                          ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n)
                                α).toUnitHom.ker ⊓
                            (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m)
                                β).toUnitHom.ker))
                        p ∧
                      (p : ℝ) < (39 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 ∧
                      (39 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 <
                        (Real.sqrt (623 / 1000) / 3 *
                            subgroupConductorLogSum
                              ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n)
                                    α).toUnitHom.ker ⊓
                                (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m)
                                    β).toUnitHom.ker)) ^
                          2 := by
  obtain ⟨Q, hQ, hb⟩ := quadratic_crt_strict_full_gain hg
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hmn hm hn hq α β hα hβ ha hb'
  exact
    ⟨NumberTheory.quadratic_crt_kernel_index α β hα hβ ha hb' hmn hn,
      hb m n hmn hm hn hq α β hα hβ ha hb'⟩

end PseudoPrime.LLS.PaperStatements
