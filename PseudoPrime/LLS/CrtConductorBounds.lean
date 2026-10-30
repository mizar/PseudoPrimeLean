/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.ConductorRatioBounds
public import PseudoPrime.LLS.RationalPoleConductorRatios
public import PseudoPrime.NumberTheory.CrtCharacters

/-! # Conductor savings and least-prime bounds for quadratic-cubic CRT kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements
/-- The product of primitive conductors of all nonprincipal characters in the
annihilator of H at a nonzero level. Erasing the principal character avoids any
convention about its conductor in later arithmetic product identities. -/
noncomputable def subgroupConductorProduct {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) : ℕ := by
  classical
  exact ∏ ψ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H), ψ.val.conductor
/-- For coprime component levels and exact orders two and three, the CRT kernel
has conductor-log sum 3log(f2)+4log(f3). Enumerate the annihilator by the six powers,
remove the principal term and use the five proved conductor identities. -/
theorem crtConductorLogSum {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (hmn : Nat.Coprime m n) :
    subgroupConductorLogSum (NumberTheory.crtKernel α β) =
      3 * Real.log α.conductor + 4 * Real.log β.conductor := by
  classical
  have hc := NumberTheory.crtCharacter_conductors α β hα hβ hmn
  rw [subgroupConductorLogSum,Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Subgroup.coe_one,DirichletCharacter.conductor_one,Nat.cast_one,Real.log_one,sub_zero]
  dsimp only [NumberTheory.crtKernel]
  rw [NumberTheory.sum_kernel_characters (NumberTheory.crtCharacter α β)
    (fun ψ : DirichletCharacter ℂ (m * n) ↦ Real.log ψ.conductor),
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log ((NumberTheory.crtCharacter α β) ^ k).conductor)
      (orderOf (NumberTheory.crtCharacter α β)),
    NumberTheory.crtCharacter_order α β hα hβ]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,
    DirichletCharacter.conductor_one,Nat.cast_one,Real.log_one,zero_add,add_zero]
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,
    Nat.cast_mul,Real.log_mul
      (Nat.cast_ne_zero.mpr α.conductor_ne_zero) (Nat.cast_ne_zero.mpr β.conductor_ne_zero)]
  ring
/-- The five nonprincipal CRT annihilator characters have conductor product f2^3*f3^4.
Enumerate all powers, whose principal conductor is one, and multiply the five exact
conductors. No list classification or conductor identity remains as a hypothesis. -/
theorem crtConductorProduct {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (hmn : Nat.Coprime m n) :
    subgroupConductorProduct (NumberTheory.crtKernel α β) =
        α.conductor ^ 3 * β.conductor ^ 4 := by
  unfold subgroupConductorProduct
  classical
  have hc := NumberTheory.crtCharacter_conductors α β hα hβ hmn
  have he := Finset.prod_erase_mul Finset.univ
    (fun ψ : NumberTheory.subgroupAnnihilator (NumberTheory.crtKernel α β) ↦ ψ.val.conductor)
    (Finset.mem_univ 1)
  simp only [Subgroup.coe_one,DirichletCharacter.conductor_one,mul_one] at he
  rw [he]
  dsimp only [NumberTheory.crtKernel]
  rw [NumberTheory.prod_kernel_characters (NumberTheory.crtCharacter α β)
    (fun ψ : DirichletCharacter ℂ (m * n) ↦ ψ.conductor),
    Fin.prod_univ_eq_prod_range (fun k : ℕ ↦ ((NumberTheory.crtCharacter α β) ^ k).conductor)
      (orderOf (NumberTheory.crtCharacter α β)),
    NumberTheory.crtCharacter_order α β hα hβ]
  norm_num only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,
    DirichletCharacter.conductor_one,mul_one,one_mul]
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2]
  ring

/-- At coprime levels, the CRT conductor-log sum is at most 4log(m*n).
Each primitive conductor divides its component level. Apply logarithm monotonicity
to the exact weighted sum and retain the nonnegative logarithm of m. -/
theorem crtConductorLogSum_le {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (hmn : Nat.Coprime m n) :
    subgroupConductorLogSum (NumberTheory.crtKernel α β) ≤ 4 * Real.log (m * n : ℕ) := by
  have ha := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero α.conductor_ne_zero))
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) α.conductor_dvd_level))
  have hb := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero β.conductor_ne_zero))
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) β.conductor_dvd_level))
  rw [crtConductorLogSum α β hα hβ hmn,Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  linarith only [ha,hb,Real.log_natCast_nonneg m]
/-- When both component characters are primitive at levels greater than one,
the exact CRT conductor sum exceeds (5/2)log(m*n). Expand the two primitive conductors
and use positive level logarithms. Thus this family is not covered by the old half-cost branch. -/
theorem crtConductorLogSum_gt_half {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (hmn : Nat.Coprime m n)
    (ha : α.IsPrimitive) (hb : β.IsPrimitive) (hm : 1 < m) (hn : 1 < n) :
    (5 / 2 : ℝ) * Real.log (m * n : ℕ) < subgroupConductorLogSum (NumberTheory.crtKernel α β) := by
  have ham : α.conductor = m := ha
  have hbn : β.conductor = n := hb
  rw [crtConductorLogSum α β hα hβ hmn,ham,hbn,Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  have hlm := Real.log_pos (Nat.one_lt_cast.mpr hm : (1 : ℝ) < m)
  have hln := Real.log_pos (Nat.one_lt_cast.mpr hn : (1 : ℝ) < n)
  linarith only [hlm,hln]
/-- Under GRH, sufficiently large coprime product levels with exact order-two and
order-three component characters satisfy the original strict Theorem 1.3 target for
the least prime outside the constructed index-six kernel. The threshold is uniform
over component levels and characters. Supply the proved CRT conductor budget to T13-A. -/
theorem theorem13_crt_two_three
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (m n : ℕ) [NeZero m] [NeZero n],
      Nat.Coprime m n → Q ≤ m * n →
      ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
        orderOf α = 2 → orderOf β = 3 →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside (m * n) (NumberTheory.crtKernel α β)) p ∧
          (p : ℝ) < (1 / 4 : ℝ) * (1 - 1 / (6 : ℝ)) ^ 2 *
            (Real.log (2 * (6 : ℝ)) / (Real.log (2 * (6 : ℝ)) - 4)) ^ 2 *
              (Real.log (m * n : ℕ)) ^ 2 := by
  obtain ⟨Q,hQ,hb⟩ := theorem13_index_six_conductor_ratio hg
  refine ⟨Q,hQ,?_⟩
  intro m n _ _ hmn hq α β hα hβ
  apply hb (m * n) hq (NumberTheory.crtKernel α β) (NumberTheory.crtKernel_index α β hα hβ)
  have hc := crtConductorLogSum_le α β hα hβ hmn
  nlinarith only [hc,Real.log_natCast_nonneg (m * n)]
/-- Under GRH, the least prime outside a quadratic-cubic CRT kernel is below
(44/125)log(m*n)^2 at sufficiently large product levels, uniformly in both components.
Use the certified rational-pole conductor coefficient 549/1000 and ratio 4/5,
then absorb a positive ambient allowance inside the strict rational margin. -/
theorem rationalPole_crt_two_three
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (m n : ℕ) [NeZero m] [NeZero n],
      Nat.Coprime m n → Q ≤ m * n →
      ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
        orderOf α = 2 → orderOf β = 3 →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside (m * n) (NumberTheory.crtKernel α β)) p ∧
          (p : ℝ) < (44 / 125 : ℝ) * (Real.log (m * n : ℕ)) ^ 2 := by
  obtain ⟨Q,hQ,hb⟩ := least_prime_bound_of_conductor_ratio (h := 6)
    (c := (549 / 1000 : ℝ)) (r := (4 / 5 : ℝ)) (C := (44 / 125 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
    (fun _ hε ↦ rationalPole_index_six_conductor hg hε)
  refine ⟨Q,hQ,?_⟩
  intro m n _ _ hmn hq α β hα hβ
  apply hb (m * n) hq (NumberTheory.crtKernel α β) (NumberTheory.crtKernel_index α β hα hβ)
  have hc := crtConductorLogSum_le α β hα hβ hmn
  nlinarith only [hc]
end PseudoPrime.LLS.PaperStatements
