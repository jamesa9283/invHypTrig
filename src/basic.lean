import analysis.special_functions.trigonometric data.real.basic analysis.special_functions.pow
import tactic

variables (x : ℝ)
open real
noncomputable theory

attribute [pp_nodot] real.log

lemma cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
eq_div_of_mul_eq two_ne_zero $ by rw [cosh, exp, exp, complex.of_real_neg, complex.cosh, mul_two,
    ← complex.add_re, ← mul_two, div_mul_cancel _ (two_ne_zero' : (2 : ℂ) ≠ 0), complex.add_re]


lemma sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
eq_div_of_mul_eq two_ne_zero $ by rw [sinh, exp, exp, complex.of_real_neg, complex.sinh, mul_two,
    ← complex.add_re, ← mul_two, div_mul_cancel _ (two_ne_zero' : (2 : ℂ) ≠ 0), complex.sub_re]


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

/-- `real.cosh` is positive-/
lemma cosh_pos (x : ℝ) : 0 < real.cosh x :=
(cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

lemma cosh_nonneg (x : ℝ) : 0 ≤ real.cosh x := le_of_lt (cosh_pos x)

lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by rw [real.deriv_sinh]; exact cosh_pos)

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [add_comm, cosh, exp_neg]

lemma sinh_nonneg (h : 0 ≤ x) : 0 ≤ sinh x :=
begin
  rw sinh_eq,
  apply div_nonneg,
  { rw [le_sub_iff_add_le, zero_add, exp_le_exp],
    linarith},
  { norm_num},
end
