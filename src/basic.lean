import analysis.special_functions.trigonometric data.real.basic analysis.special_functions.pow

open real
noncomputable theory

local attribute [pp_nodot] real.log

lemma cosh_def (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
by simp only [cosh, complex.cosh, complex.div_re, complex.exp_of_real_re, complex.one_re, 
  bit0_zero, add_zero, complex.add_re, euclidean_domain.zero_div, complex.bit0_re,
  complex.one_im, complex.bit0_im, mul_zero, ← complex.of_real_neg, complex.norm_sq];
  ring

lemma sinh_def (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
by simp only [sinh, complex.sinh, complex.div_re, complex.exp_of_real_re, complex.one_re, 
  bit0_zero, add_zero, complex.sub_re, euclidean_domain.zero_div, complex.bit0_re,
  complex.one_im, complex.bit0_im, mul_zero, ← complex.of_real_neg, complex.norm_sq];
  ring


lemma cosh_pos (x : ℝ) : 0 < real.cosh x :=
(cosh_def x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by rw [real.deriv_sinh]; exact cosh_pos)
