/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: James Arthur, Chris Hughes, Shing Tak Lam.
-/
import basic
open real
noncomputable theory

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh. 

## Main Results

- `sinm_injective`: The proof that `sinm` is injective
- `sinm_surjective`: The proof that `sinm` is surjective
- `sinm_bijective`: The proof `sinm` is bijective

## Notation 

- `arsinh`: The inverse function of `sinm`

## Tags

arsinh, sinh injective, sinh bijective, sinh surjective
-/

/-- The inverse of the `sinh`-/
def arsinh (x : ℝ) := log (x + sqrt(1 + x^2)) 


/-- Proving that `∀ a b, sinh a = sinh b → a = b` -/
lemma sinh_injective : function.injective sinh := sinh_strict_mono.injective

private lemma aux_lemma (x : ℝ) : 1/(x + (1 + x^2).sqrt) = - x + (1 + x^2).sqrt :=
begin
  have H : (x - (1 + x^2).sqrt)/((x - (1 + x^2).sqrt) * (x + (1 + x^2).sqrt)) = -x + (1 + x^2).sqrt,
  { have G : (x - (1 + x^2).sqrt) * (x + (1 + x^2).sqrt) = -1,
    { ring,
      rw sqr_sqrt,
      { ring },
      { linarith [pow_two_nonneg x]} },
    rw G,
    ring },
  rw [division_def, mul_inv', ←mul_assoc, mul_comm (x - sqrt (1 + x ^ 2)), inv_mul_cancel] at H,
  rw one_mul at H,
  rw [division_def, one_mul],
  exact H,
  { intros fx,
    rw sub_eq_zero at fx,
    have fx_sq : x^2 = (sqrt (1 + x ^ 2)) ^ 2 := by { rw fx.symm },
    rw sqr_sqrt at fx_sq,
    linarith,
    have G : 0 ≤ x^2 := by {apply pow_two_nonneg},
    linarith }
end

private lemma b_lt_sqrt_b_sq_add_one (b : ℝ) : b < sqrt(b^2 + 1) :=
begin
  by_cases hb : 0 ≤ b,
  conv { to_lhs, rw ← sqrt_sqr hb },
  rw sqrt_lt,
  linarith,
  apply pow_two_nonneg,
  have F : 0 ≤ b^2 := by { apply pow_two_nonneg },
  linarith,
  rw not_le at hb,
  apply lt_of_lt_of_le hb,
  apply sqrt_nonneg,
end

/-- Proving `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b` -/
lemma sinh_surjective : function.surjective sinh :=
begin
  intro b,
  use (arsinh b),
  rw sinh_def,
  unfold arsinh,
  rw ←log_inv,
  rw [exp_log, exp_log],
  { rw [← one_mul ((b + sqrt (1 + b ^ 2))⁻¹), ←division_def, aux_lemma],
    ring },
  { rw [← one_mul ((b + sqrt (1 + b ^ 2))⁻¹), ←division_def, aux_lemma],
    ring,
    rw [neg_add_eq_sub, sub_pos],
    have H : b^2 < sqrt (b ^ 2 + 1)^2,
    { rw sqr_sqrt,
      linarith,
      have F : 0 ≤ b^2 := by {apply pow_two_nonneg},
      linarith },
    exact b_lt_sqrt_b_sq_add_one b,
  },
  { have H := b_lt_sqrt_b_sq_add_one (-b),
    rw [neg_square, add_comm (b^2)] at H,
    linarith },
end

/-- Proving that `sinh` is both injective and surjective-/
lemma sinh_bijective : function.bijective sinh := 
⟨sinh_injective, sinh_surjective⟩

/-- A real version of `complex.cosh_sq_sub_sinh_sq`-/
lemma real.cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 :=
begin
  rw [sinh, cosh],
  have := complex.cosh_sq_sub_sinh_sq x,
  apply_fun complex.re at this,
  rw [pow_two, pow_two] at this,
  change (⟨_, _⟩ : ℂ).re - (⟨_, _⟩ : ℂ).re = 1 at this,
  rw [complex.cosh_of_real_im x, complex.sinh_of_real_im x] at this,
  norm_num at this,
  rwa [pow_two, pow_two],
end

/-- A rearrangment and `sqrt` of `real.cosh_sq_sub_sinh_sq` -/
lemma sqrt_one_add_sinh_sq (x : ℝ): sqrt (1 + sinh x ^ 2) = cosh x := 
begin
  have H := real.cosh_sq_sub_sinh_sq x,
  have G : cosh x ^ 2 - sinh x ^ 2 + sinh x ^ 2 = 1 + sinh x ^ 2 := by {rw H},
  ring at G,
  rw add_comm at G,
  rw [G.symm, sqrt_sqr],
  exact le_of_lt (cosh_pos x),
end

/-- Proving that `arsinh` is a left inverse of `sinh` -/
lemma sinh_arsinh (x : ℝ) : arsinh (sinh x) = x :=
begin
  unfold arsinh,
  rw sinh_def,
  apply exp_injective,
  rw exp_log,
  { rw [← sinh_def, sqrt_one_add_sinh_sq, cosh_def, sinh_def],
    ring },
  { rw [← sinh_def, sqrt_one_add_sinh_sq, cosh_def, sinh_def],
    ring,
    exact exp_pos x },
end

lemma arsinh_sinh (x : ℝ) : sinh (arsinh x) = x :=
begin
  rw sinh_def,
  unfold arsinh,
  rw ←log_inv,
  rw [exp_log, exp_log],
  { rw [← one_mul ((x + sqrt (1 + x ^ 2))⁻¹), ←division_def, aux_lemma],
    ring },
  { rw [← one_mul ((x + sqrt (1 + x ^ 2))⁻¹), ←division_def, aux_lemma],
    ring,
    rw [neg_add_eq_sub, sub_pos],
    have H : x^2 < sqrt (x ^ 2 + 1)^2,
    { rw sqr_sqrt,
      linarith,
      have F : 0 ≤ x^2 := by {apply pow_two_nonneg},
      linarith },
    exact b_lt_sqrt_b_sq_add_one x,
  },
  { have H := b_lt_sqrt_b_sq_add_one (-x),
    rw [neg_square, add_comm (x^2)] at H,
    linarith },
end