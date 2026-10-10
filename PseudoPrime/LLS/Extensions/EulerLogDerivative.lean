/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.OrdinaryEndpoint

/-!
# Local Euler logarithmic derivatives

The Ramanujan root bound gives pole-free factors and convergent geometric expansions.
Summing over primes and differentiating the infinite product remain separate analytic steps.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible roots, a prime p and a complex s with Re s > 0, the norm of
root(p,j)/p^s is less than one. The denominator has norm p^(Re s) > 1 and the root
has norm at most one. This justifies nonvanishing and geometric-series expansions. -/
theorem norm_root_div_prime_cpow_lt_one (f : GeneralLFunction) (hf : f.IsAdmissible)
    (p : Nat.Primes) (j : Fin f.degree) {s : ℂ} (hs : 0 < s.re) :
    ‖f.root p j / (p : ℂ) ^ s‖ < 1 := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hpow : 1 < ‖(p : ℂ) ^ s‖ := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos]
    exact Real.one_lt_rpow hp hs
  rw [norm_div]
  exact (div_lt_one (lt_trans zero_lt_one hpow)).mpr ((hf.2.2.2.2.1 p p.property j).trans_lt hpow)

/-- For admissible data, a prime p and Re s > 0, the denominator 1 - root(p,j)/p^s is
nonzero. Its subtracted term has norm less than one, so it cannot equal one.
This permits differentiation and inversion of each local Euler root factor. -/
theorem one_sub_root_div_prime_cpow_ne_zero (f : GeneralLFunction) (hf : f.IsAdmissible)
    (p : Nat.Primes) (j : Fin f.degree) {s : ℂ} (hs : 0 < s.re) :
    1 - f.root p j / (p : ℂ) ^ s ≠ 0 := by
  intro hz
  have he : f.root p j / (p : ℂ) ^ s = 1 := (sub_eq_zero.mp hz).symm
  have hn := norm_root_div_prime_cpow_lt_one f hf p j hs
  rw [he, norm_one] at hn
  exact lt_irrefl _ hn

/-- For admissible data, a prime p and Re s > 0, the logarithmic derivative of the root
factor (1 - root(p,j)/p^s)^(-1) is -u * log(p)/(1-u), where u = root(p,j)/p^s.
Differentiate the complex power, quotient and inverse; the denominator norm bound
justifies the divisions. This is the single-root input to the finite Euler factor. -/
theorem logDeriv_localEulerRoot (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes)
    (j : Fin f.degree) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z : ℂ ↦ (1 - f.root p j / (p : ℂ) ^ z)⁻¹) s =
      -(f.root p j / (p : ℂ) ^ s) * Complex.log (p : ℕ) / (1 - f.root p j / (p : ℂ) ^ s) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hpow := (hasDerivAt_id s).const_cpow (Or.inl hp)
  simp only [id_eq, mul_one] at hpow
  have hd :=
    ((hasDerivAt_const s (f.root p j)).div hpow
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))).const_sub
      1
  have hne := one_sub_root_div_prime_cpow_ne_zero f hf p j hs
  have hi := hd.inv hne
  simp only [Pi.div_apply, Pi.inv_def] at hi
  rw [logDeriv_apply, hi.deriv]
  field_simp [hne, Complex.cpow_ne_zero_iff.mpr (Or.inl hp)]
  ring

/-- For admissible data, a prime p and Re s > 0, each local Euler root factor is complex
differentiable at s. Differentiate the nonzero complex power, complementary denominator
and inverse. This verifies the differentiability hypothesis for the product rule
for logarithmic derivatives. -/
theorem differentiableAt_localEulerRoot (f : GeneralLFunction) (hf : f.IsAdmissible)
    (p : Nat.Primes) (j : Fin f.degree) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ (1 - f.root p j / (p : ℂ) ^ z)⁻¹) s := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hd :=
    ((differentiableAt_const (x := s) (f.root p j)).div
          ((differentiableAt_id (x := s)).const_cpow (Or.inl hp))
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))).const_sub
      1
  have hi := hd.inv (one_sub_root_div_prime_cpow_ne_zero f hf p j hs)
  simpa only [Pi.div_apply, Pi.inv_def, id_eq] using hi

/-- For admissible data, a prime p and Re s > 0, the logarithmic derivative of the Euler
factor is the finite sum of -u * log(p)/(1-u) over its roots, with u = root(p,j)/p^s.
Each root factor is nonzero and differentiable, so the logarithmic derivative product
rule applies. This finite rational expression is then expanded as geometric series. -/
theorem logDeriv_eulerFactor (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (f.eulerFactor p) s =
      ∑ j : Fin f.degree,
        -(f.root p j / (p : ℂ) ^ s) * Complex.log (p : ℕ) / (1 - f.root p j / (p : ℂ) ^ s) := by
  have he :
    f.eulerFactor p = ∏ j : Fin f.degree, (fun z : ℂ ↦ (1 - f.root p j / (p : ℂ) ^ z)⁻¹) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  rw [he,
    logDeriv_prod (f := fun j : Fin f.degree ↦ fun z : ℂ ↦ (1 - f.root p j / (p : ℂ) ^ z)⁻¹) (x :=
      s) (fun j _ ↦ inv_ne_zero (one_sub_root_div_prime_cpow_ne_zero f hf p j hs))
      (fun j _ ↦ differentiableAt_localEulerRoot f hf p j hs)]
  exact Finset.sum_congr rfl (fun j _ ↦ logDeriv_localEulerRoot f hf p j hs)

/-- For admissible data, a prime p and Re s > 0, expand the Euler factor's logarithmic
derivative as the finite root sum of -log(p) times the geometric series with terms
(root(p,j)/p^s)^(k+1). Each ratio has norm less than one, which ensures convergence
and identifies its sum with u/(1-u). This is the local input to the global prime-power series. -/
theorem logDeriv_eulerFactor_eq_geometric_series (f : GeneralLFunction) (hf : f.IsAdmissible)
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (f.eulerFactor p) s =
      ∑ j : Fin f.degree,
        -Complex.log (p : ℕ) * ∑' k : ℕ, (f.root p j / (p : ℂ) ^ s) ^ (k + 1) := by
  rw [logDeriv_eulerFactor f hf p hs]
  apply Finset.sum_congr rfl
  intro j _
  have he :
    (∑' k : ℕ, (f.root p j / (p : ℂ) ^ s) ^ (k + 1)) =
      (f.root p j / (p : ℂ) ^ s) * (1 - f.root p j / (p : ℂ) ^ s)⁻¹ := by
    simp only [pow_succ', tsum_mul_left,
      tsum_geometric_of_norm_lt_one (norm_root_div_prime_cpow_lt_one f hf p j hs)]
  rw [he, div_eq_mul_inv]
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
