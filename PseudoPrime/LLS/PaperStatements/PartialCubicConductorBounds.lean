/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.PartialQuadraticConductorBounds
public import PseudoPrime.LLS.PaperStatements.CrtConductorBounds

/-! # Quadratic-cubic partial-family conductor bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, the existing index-three gamma certificate yields the exact
conductor-sensitive radius with coefficient 7/10 and any positive ambient
allowance. Use the certified scale 81/40; the threshold is uniform in the
modulus and subgroup, including bounded primitive conductors. -/
theorem gamma_cubic_conductor (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ J : Subgroup (ZMod q)ˣ,
              J.index = 3 →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q J) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt (7 / 10) / ((3 : ℝ) - 1) * subgroupConductorLogSum J +
                          ε * Real.log q) ^
                        2 := by
  have hd : 0 < (3 : ℝ) - 1 - 3 * Real.exp (-(81 / 40 : ℝ)) := by
    have he := gamma_three_exp_bound
    linarith only [he]
  have h3 : (3 : ℝ) - 1 = 2 := by norm_num only
  have ht :=
    gamma_prime_bound_of_conductor_certificate hg 3 (by norm_num only) (l := (81 / 40 : ℝ)) (c :=
      (7 / 10 : ℝ)) (by norm_num only) (by norm_num only) hε hd
      (by simpa only [Nat.cast_ofNat, h3] using gamma_three_coefficient)
  simpa only [Nat.cast_ofNat] using ht

/-- Under GRH, an index-two and an index-three supergroup whose normalized
conductor costs total at most log q give a strict 37/200 log(q)^2 bound
outside any common subgroup. Split at the rational conductor ratio 487/1000;
each resulting kernel certificate leaves a strict uniform allowance. -/
theorem quadratic_cubic_partial_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ J₂ J₃ H : Subgroup (ZMod q)ˣ,
              J₂.index = 2 →
                J₃.index = 3 →
                H ≤ J₂ →
                H ≤ J₃ →
                subgroupConductorLogSum J₂ + subgroupConductorLogSum J₃ / 2 ≤ Real.log q →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q H) p ∧
                    (p : ℝ) < (37 / 200 : ℝ) * Real.log q ^ 2 := by
  obtain ⟨Q₂, hQ₂, hb₂⟩ :=
    least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 2)
      (by norm_num only : (0 : ℝ) < 777 / 1000) (by norm_num only : (0 : ℝ) ≤ 487 / 1000)
      (by norm_num only : (777 / 1000 : ℝ) * (487 / 1000) ^ 2 < 37 / 200)
      (fun _ hε ↦ rationalPole_quadratic_conductor hg hε)
  obtain ⟨Q₃, hQ₃, hb₃⟩ :=
    least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 3)
      (by norm_num only : (0 : ℝ) < 7 / 10) (by norm_num only : (0 : ℝ) ≤ 513 / 1000)
      (by norm_num only : (7 / 10 : ℝ) * (513 / 1000) ^ 2 < 37 / 200)
      (fun _ hε ↦ gamma_cubic_conductor hg hε)
  refine ⟨max Q₂ Q₃, hQ₂.trans (le_max_left _ _), ?_⟩
  intro q _ hq J₂ J₃ H hi₂ hi₃ hH₂ hH₃ hsum
  have htransfer (J : Subgroup (ZMod q)ˣ) (hHJ : H ≤ J) {p : ℕ}
    (hp : p ∈ NumberTheory.primesOutside q J) :
    ∃ r : ℕ, IsLeast (NumberTheory.primesOutside q H) r ∧ r ≤ p := by
    classical
    have hpH : p ∈ NumberTheory.primesOutside q H :=
      ⟨hp.1, hp.2.1, fun ⟨u, hu, he⟩ ↦ hp.2.2 ⟨u, hHJ hu, he⟩⟩
    have hn : ∃ r : ℕ, r ∈ NumberTheory.primesOutside q H := ⟨p, hpH⟩
    exact ⟨Nat.find hn, ⟨Nat.find_spec hn, fun _ hr ↦ Nat.find_min' hn hr⟩, Nat.find_min' hn hpH⟩
  have hq₂ := (le_max_left Q₂ Q₃).trans hq
  have hq₃ := (le_max_right Q₂ Q₃).trans hq
  by_cases hs : subgroupConductorLogSum J₂ ≤ (487 / 1000 : ℝ) * Real.log q
  · obtain ⟨p, hp, hpb⟩ := hb₂ q hq₂ J₂ hi₂ (by nlinarith only [hs])
    obtain ⟨r, hr, hrp⟩ := htransfer J₂ hH₂ hp.1
    exact ⟨r, hr, (Nat.cast_le.mpr hrp).trans_lt hpb⟩
  · obtain ⟨p, hp, hpb⟩ := hb₃ q hq₃ J₃ hi₃ (by linarith only [hs, hsum])
    obtain ⟨r, hr, hrp⟩ := htransfer J₃ hH₃ hp.1
    exact ⟨r, hr, (Nat.cast_le.mpr hrp).trans_lt hpb⟩

/-- For a character of exact order three, its unit kernel has conductor-log
sum twice log conductor. Enumerate the three annihilator powers and use that
the nonprincipal powers are the character and its inverse with equal conductor. -/
theorem cubic_kernel_conductor_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : orderOf χ = 3) : subgroupConductorLogSum χ.toUnitHom.ker = 2 * Real.log χ.conductor := by
  classical
  have hp : χ ^ 2 = χ⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr
      (by
        rw [← pow_succ]; change χ ^ 3 = 1; rw [← hχ, pow_orderOf_eq_one])
  rw [subgroupConductorLogSum, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Subgroup.coe_one, DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one,
    sub_zero]
  rw [NumberTheory.sum_kernel_characters χ (fun ψ : DirichletCharacter ℂ q ↦ Real.log ψ.conductor),
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log (χ ^ k).conductor) (orderOf χ), hχ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, hp,
    DirichletCharacter.conductor_inv, DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one,
    zero_add, add_zero]
  ring

/-- Under GRH, every sufficiently large nonzero product level with quadratic
and cubic component characters has an actual index-six CRT kernel whose
least outside prime is below 37/200 log(m*n)^2. Apply the two partial families
and their exact conductor sums; each conductor divides its component level.
No primitivity or coprimality hypothesis is needed for this branch. -/
theorem crt_two_three_partial_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (m n : ℕ) [NeZero m] [NeZero n],
          Q ≤ m * n →
            ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
              orderOf α = 2 →
                orderOf β = 3 →
                (NumberTheory.crtKernel α β).index = 6 ∧
                  ∃ p : ℕ,
                    IsLeast (NumberTheory.primesOutside (m * n) (NumberTheory.crtKernel α β)) p ∧
                      (p : ℝ) < (37 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 := by
  obtain ⟨Q, hQ, hbound⟩ := quadratic_cubic_partial_bound hg
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hq α β hα hβ
  refine ⟨NumberTheory.crtKernel_index α β hα hβ, ?_⟩
  let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
  let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
  have ha : orderOf a = 2 :=
    (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
          (DirichletCharacter.changeLevel_injective _) α).trans
      hα
  have hb : orderOf b = 3 :=
    (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
          (DirichletCharacter.changeLevel_injective _) β).trans
      hβ
  rw [NumberTheory.crtKernel_eq_inf α β hα hβ]
  apply
    hbound (m * n) hq a.toUnitHom.ker b.toUnitHom.ker _
      ((NumberTheory.index_kernel_eq_order a).trans ha)
      ((NumberTheory.index_kernel_eq_order b).trans hb) inf_le_left inf_le_right
  rw [quadratic_kernel_conductor_sum a ha, cubic_kernel_conductor_sum b hb]
  have hca : a.conductor = α.conductor := DirichletCharacter.conductor_changeLevel α _
  have hcb : b.conductor = β.conductor := DirichletCharacter.conductor_changeLevel β _
  rw [hca, hcb, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  have hma :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero α.conductor_ne_zero))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) α.conductor_dvd_level))
  have hnb :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero β.conductor_ne_zero))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) β.conductor_dvd_level))
  linarith only [hma, hnb]

/-- For a positive ambient log scale and full index-six conductor sum at
least three times that scale, the partial-family coefficient 37/200 is
strictly below the full rational-pole main radius with coefficient 549/1000.
Retain any nonnegative ambient allowance and compare nonnegative squares.
This supplies the strict comparison for primitive quadratic-cubic CRT families. -/
theorem cubic_partial_strict_gain {L S η : ℝ} (hL : 0 < L) (hS : 3 * L ≤ S) (hη : 0 ≤ η) :
    (37 / 200 : ℝ) * L ^ 2 < (Real.sqrt (549 / 1000) / 5 * S + η * L) ^ 2 := by
  have hpos : 0 ≤ S := (mul_pos (by norm_num only : (0 : ℝ) < 3) hL).le.trans hS
  have hm := mul_self_le_mul_self (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hL.le) hS
  have hr : 0 ≤ Real.sqrt (549 / 1000) / 5 * S :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num only)) hpos
  have hs := mul_self_le_mul_self hr (le_add_of_nonneg_right (mul_nonneg hη hL.le))
  have hid : (Real.sqrt (549 / 1000) / 5 * S) ^ 2 = (549 / 25000 : ℝ) * S ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 549 / 1000)]
    ring
  nlinarith only [hm, hs, hid, sq_pos_of_pos hL]

/-- Under GRH, primitive quadratic and cubic characters at coprime nonzero
levels define an actual index-six CRT kernel whose least outside prime obeys
the 37/200 bound. Its bound is strictly below the full 549/1000 conductor
main radius. Exact conductor logs give the lower bound three log(m*n).
The threshold is uniform over components and characters and remains existential. -/
theorem crt_two_three_strict_full_gain
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (m n : ℕ) [NeZero m] [NeZero n],
          Nat.Coprime m n →
            Q ≤ m * n →
            ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
              orderOf α = 2 →
                orderOf β = 3 →
                α.IsPrimitive →
                β.IsPrimitive →
                (NumberTheory.crtKernel α β).index = 6 ∧
                  ∃ p : ℕ,
                    IsLeast (NumberTheory.primesOutside (m * n) (NumberTheory.crtKernel α β)) p ∧
                      (p : ℝ) < (37 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 ∧
                      (37 / 200 : ℝ) * Real.log (m * n : ℕ) ^ 2 <
                        (Real.sqrt (549 / 1000) / 5 *
                            subgroupConductorLogSum (NumberTheory.crtKernel α β)) ^
                          2 := by
  obtain ⟨Q, hQ, hb⟩ := crt_two_three_partial_bound hg
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hmn hq α β hao hbo ha hb'
  obtain ⟨hi, p, hp, hpb⟩ := hb m n hq α β hao hbo
  have hl : 0 < Real.log (m * n : ℕ) :=
    Real.log_pos (Nat.one_lt_cast.mpr ((by norm_num only : 1 < 20000).trans_le (hQ.trans hq)))
  have hc : 3 * Real.log (m * n : ℕ) ≤ subgroupConductorLogSum (NumberTheory.crtKernel α β) := by
    rw [crtConductorLogSum α β hao hbo hmn, ha, hb', Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m)) (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    linarith only [Real.log_natCast_nonneg n]
  have hs := cubic_partial_strict_gain hl hc (le_refl (0 : ℝ))
  exact ⟨hi, p, hp, hpb, by simpa only [zero_mul, add_zero] using hs⟩

end PseudoPrime.LLS.PaperStatements
