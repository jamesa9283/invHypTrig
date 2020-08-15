import analysis.special_functions.trigonometric data.real.basic analysis.special_functions.pow

#print real.sinh
--variables (x : ℝ)
open real
noncomputable theory

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

lemma one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
begin
    have cosh_zero_eq_one : cosh 0 = 1 := by {rw cosh_zero},
    have sinh_zero_eq_zero : sinh 0 = 0 := by {rw sinh_zero},
    have sinh_strict_mono : strict_mono sinh := sinh_strict_mono,
    have deriv_cosh : deriv cosh = sinh := by {rw real.deriv_cosh},
    sorry
end

lemma le_add_of_pos_le (a b c : ℝ) ( h : a ≤ c) (fc : 0 ≤ c) (fb : 0 ≤ b) (g : a ≤ b) :  a ≤ b + c := by linarith

lemma one_le_cosh' (x : ℝ) : 1/2 ≤ cosh x :=
begin
  rw cosh_def,
  rw div_le_iff,
  {
      rw div_mul_cancel,
      {
        sorry
          /-
x : ℝ
⊢ 1 < exp x + exp (-x)
-/
      },
      {norm_num}
  },
  {norm_num}
end


lemma sinh_injective : function.injective sinh := sinh_strict_mono.injective

def arsinh (x : ℝ) := log (x + sqrt(1 + x^2)) 

lemma rat_dom_cool_trick (x : ℝ) : 1/(x + (1 + x^2).sqrt) = - x + (1 + x^2).sqrt :=
begin
  have H : (x - (1 + x^2).sqrt)/((x - (1 + x^2).sqrt) * (x + (1 + x^2).sqrt)) = - x + (1 + x^2).sqrt,
  {
    have G : (x - (1 + x^2).sqrt) * (x + (1 + x^2).sqrt) = -1,
    {
      ring,
      rw sqr_sqrt,
      {ring},
      {linarith [pow_two_nonneg x]},
    },
    rw G,
    ring,
  },
  rw [division_def, mul_inv', ←mul_assoc, mul_comm (x - sqrt (1 + x ^ 2)), inv_mul_cancel, one_mul] at H,
  rw [division_def, one_mul],
  exact H,
  {
    -- x - sqrt(1 + x^2) ≠ 0
    intros fx,
    rw sub_eq_zero at fx,
    have fx_sq : x^2 = (sqrt (1 + x ^ 2)) ^ 2,
    {rw fx.symm},
    rw sqr_sqrt at fx_sq,
    linarith,
    have G : 0 ≤ x^2 := by {apply pow_two_nonneg},
    linarith,
  }
end

lemma sinh_surjective : function.surjective sinh :=
begin
  unfold function.surjective,
  intro b,
  use (arsinh b),
  rw sinh_def,
  unfold arsinh,
  rw ←log_inv,
  repeat{rw exp_log},
  {
    rw ← one_mul ((b + sqrt (1 + b ^ 2))⁻¹),
    rw ←division_def,
    rw rat_dom_cool_trick,
    ring,
  },
  {
    rw ← one_mul ((b + sqrt (1 + b ^ 2))⁻¹),
    rw ←division_def,
    rw rat_dom_cool_trick,
    ring,
    sorry
  },
  {
    have G : b^2 < (sqrt(1 + b^2))^2,
    {
      rw sqr_sqrt,
      {linarith},
      {
        have F : 0 ≤ b^2 := by {apply pow_two_nonneg},
        linarith,
      }
    },
    sorry
  },

end


--example (x : ℝ) : 1 ≤ cosh x := by library_search

