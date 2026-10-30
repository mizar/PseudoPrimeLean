/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.RationalPolePrimeBounds
public import PseudoPrime.NumberTheory.CharacterKernelOrder
public import PseudoPrime.NumberTheory.QuadraticCrtKernels

/-! # Partial quadratic character families and least outside primes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For an exact order-two character, the nonprincipal annihilator conductor
sum of its unit kernel is its own conductor logarithm. Enumerate the two
kernel characters and remove the principal term. This supplies the exact
budget for the rational-pole bound on a selected quadratic subfamily. -/
theorem quadratic_kernel_conductor_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 2) :
    subgroupConductorLogSum χ.toUnitHom.ker = Real.log χ.conductor := by
  classical
  rw [subgroupConductorLogSum, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Subgroup.coe_one, DirichletCharacter.conductor_one, Nat.cast_one,
    Real.log_one, sub_zero]
  rw [NumberTheory.sum_kernel_characters χ
    (fun ψ : DirichletCharacter ℂ q ↦ Real.log ψ.conductor),
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log (χ ^ k).conductor) (orderOf χ), ho]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one, zero_add]

/-- Under GRH, any subgroup contained in two quadratic unit kernels has an
actual least outside prime bounded by the smaller of their exact conductor
radii. The positive ambient allowance is retained. Apply the certified
index-two bound twice and minimize the eligible outside-prime set. The threshold
is uniform over moduli, target subgroups and both selected characters. -/
theorem quadratic_partial_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ (H : Subgroup (ZMod q)ˣ) (a b : DirichletCharacter ℂ q),
        orderOf a = 2 → orderOf b = 2 →
        H ≤ a.toUnitHom.ker → H ≤ b.toUnitHom.ker →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          min ((Real.sqrt (777 / 1000) * Real.log a.conductor + ε * Real.log q) ^ 2)
            ((Real.sqrt (777 / 1000) * Real.log b.conductor + ε * Real.log q) ^ 2) := by
  classical
  obtain ⟨Q, hQ, hb⟩ := rationalPole_quadratic_conductor hg hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hao hbo haH hbH
  obtain ⟨pa, hpa, hba⟩ := hb q hq a.toUnitHom.ker
    ((NumberTheory.index_kernel_eq_order a).trans hao)
  obtain ⟨pb, hpb, hbb⟩ := hb q hq b.toUnitHom.ker
    ((NumberTheory.index_kernel_eq_order b).trans hbo)
  norm_num only [quadratic_kernel_conductor_sum a hao, div_one] at hba
  norm_num only [quadratic_kernel_conductor_sum b hbo, div_one] at hbb
  have hmem (χ : DirichletCharacter ℂ q) (hH : H ≤ χ.toUnitHom.ker)
      {p : ℕ} (hp : p ∈ NumberTheory.primesOutside q χ.toUnitHom.ker) : p ∈
        NumberTheory.primesOutside q H := by
    refine ⟨hp.1, hp.2.1, ?_⟩
    rintro ⟨u, hu, he⟩
    exact hp.2.2 ⟨u, hH hu, he⟩
  have hpaH := hmem a haH hpa.1
  have hpbH := hmem b hbH hpb.1
  have hn : ∃ p : ℕ, p ∈ NumberTheory.primesOutside q H := ⟨pa, hpaH⟩
  refine ⟨Nat.find hn, ⟨Nat.find_spec hn, fun _ hr ↦ Nat.find_min' hn hr⟩, ?_⟩
  exact le_min ((Nat.cast_le.mpr (Nat.find_min' hn hpaH)).trans hba)
    ((Nat.cast_le.mpr (Nat.find_min' hn hpbH)).trans hbb)

/-- Under GRH, if at least one selected quadratic conductor has logarithm
at most r log(q), every coefficient C greater than (777/1000)r^2 bounds the
actual least prime outside a subgroup contained in both kernels. Choose a
positive ambient allowance inside the strict coefficient margin and use
the smaller conductor radius. The threshold is uniform over the characters. -/
theorem quadratic_partial_ratio_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r C : ℝ} (hr : 0 ≤ r) (hcoef : (777 / 1000 : ℝ) * r ^ 2 < C) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ (H : Subgroup (ZMod q)ˣ) (a b : DirichletCharacter ℂ q),
        orderOf a = 2 → orderOf b = 2 →
        H ≤ a.toUnitHom.ker → H ≤ b.toUnitHom.ker →
        min (Real.log a.conductor) (Real.log b.conductor) ≤ r * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < C * (Real.log q) ^ 2 := by
  obtain ⟨ε, hε, hgap⟩ := exists_conductor_ratio_allowance
    (by norm_num only : (0 : ℝ) < 777 / 1000) hr hcoef
  obtain ⟨Q, hQ, hb⟩ := quadratic_partial_min_radius hg hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hao hbo haH hbH hcost
  obtain ⟨p, hp, hpb⟩ := hb q hq H a b hao hbo haH hbH
  have hl : 0 < Real.log q := Real.log_pos
    (Nat.one_lt_cast.mpr ((by norm_num only : 1 < 20000).trans_le (hQ.trans hq)))
  have hs (S : ℝ) (hS : 0 ≤ S) (hSr : S ≤ r * Real.log q) :
      (Real.sqrt (777 / 1000) * S + ε * Real.log q) ^ 2 < C * (Real.log q) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hSr (Real.sqrt_nonneg (777 / 1000 : ℝ))
    have hsq := mul_self_le_mul_self
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hS) (mul_nonneg hε.le hl.le))
      (by nlinarith only [hm] : Real.sqrt (777 / 1000) * S + ε * Real.log q ≤
        (r * Real.sqrt (777 / 1000) + ε) * Real.log q)
    have ht := mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hl)
    nlinarith only [hsq, ht]
  rcases le_total (Real.log a.conductor) (Real.log b.conductor) with hab | hba
  · rw [min_eq_left hab] at hcost
    exact ⟨p, hp, (hpb.trans (min_le_left _ _)).trans_lt
      (hs _ (Real.log_natCast_nonneg _) hcost)⟩
  · rw [min_eq_right hba] at hcost
    exact ⟨p, hp, (hpb.trans (min_le_right _ _)).trans_lt
      (hs _ (Real.log_natCast_nonneg _) hcost)⟩

/-- Under GRH, if the two selected quadratic conductor logarithms sum to at
most log(q), their cheaper branch has conductor ratio at most one half.
Every C greater than 777/4000 therefore bounds the actual least outside prime
by C log(q)^2, uniformly over subgroups contained in both kernels. -/
theorem quadratic_partial_half_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {C : ℝ} (hC : (777 / 4000 : ℝ) < C) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ (H : Subgroup (ZMod q)ˣ) (a b : DirichletCharacter ℂ q),
        orderOf a = 2 → orderOf b = 2 →
        H ≤ a.toUnitHom.ker → H ≤ b.toUnitHom.ker →
        Real.log a.conductor + Real.log b.conductor ≤ Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < C * (Real.log q) ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ := quadratic_partial_ratio_bound hg (C := C)
    (by norm_num only : (0 : ℝ) ≤ 1 / 2) (by nlinarith only [hC])
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hao hbo haH hbH hsum
  apply hb q hq H a b hao hbo haH hbH
  linarith only [min_le_left (Real.log a.conductor) (Real.log b.conductor),
    min_le_right (Real.log a.conductor) (Real.log b.conductor), hsum]

/-- Under GRH, two primitive order-two characters at coprime nonzero levels
define a concrete index-four CRT kernel. Every C greater than 777/4000 bounds
its actual least eligible outside prime by C log(m*n)^2 for sufficiently large
product levels, uniformly in the components. Exact conductors make their log
sum log(m*n), so the cheaper quadratic family supplies the half-ratio bound. -/
theorem quadratic_crt_partial_bound (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {C : ℝ} (hC : (777 / 4000 : ℝ) < C) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (m n : ℕ) [NeZero m] [NeZero n], Q ≤ m * n →
      ∀ (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n),
        orderOf α = 2 → orderOf β = 2 → α.IsPrimitive → β.IsPrimitive →
        Nat.Coprime m n → 1 < n →
        let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
        let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
        let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
        H.index = 4 ∧ ∃ p : ℕ, IsLeast (NumberTheory.primesOutside (m * n) H) p ∧
          (p : ℝ) < C * (Real.log (m * n : ℕ)) ^ 2 := by
  obtain ⟨Q, hQ, hbound⟩ := quadratic_partial_half_bound hg hC
  refine ⟨Q, hQ, ?_⟩
  intro m n _ _ hq α β hao hbo ha hb hmn hn a b H
  refine ⟨NumberTheory.quadratic_crt_kernel_index α β hao hbo ha hb hmn hn, ?_⟩
  apply hbound (m * n) hq H a b
  · exact (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
      (DirichletCharacter.changeLevel_injective _) α).trans hao
  · exact (orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
      (DirichletCharacter.changeLevel_injective _) β).trans hbo
  · exact inf_le_left
  · exact inf_le_right
  · change Real.log (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).conductor +
      Real.log (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).conductor ≤ _
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
      ha, hb, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne m))
        (Nat.cast_ne_zero.mpr (NeZero.ne n))]

end PseudoPrime.LLS.PaperStatements
