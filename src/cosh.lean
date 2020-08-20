import basic analysis.convex.extrema sinh

open real
noncomputable theory

def arcosh (x : ℝ) := log (x + sqrt(x^2 - 1))

lemma arcosh_eq (x : ℝ) : arcosh x = log (x + sqrt(x^2 - 1)) := rfl

lemma half_le_cosh (x : ℝ)  (h : 0 ≤ x) : 1/2 ≤ cosh x :=
begin
    rw cosh_eq,
    apply div_le_div,
    { linarith [exp_pos x, exp_pos (-x)]},
    { have H : 1 ≤ exp x := by {convert exp_monotone h, rw exp_zero},
      linarith [exp_pos (-x)]},
    { norm_num},
    { norm_num}
end

private lemma h' (b : ℝ) (h : 1 ≤ b) : 0 ≤ b := by linarith


private lemma cos_sq (x : ℝ) : cosh x ^ 2 = 1 + sinh x ^ 2 := 
    eq_add_of_sub_eq (cosh_sq_sub_sinh_sq x)

lemma one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
begin
  have G : 1 ≤ cosh x ^ 2,
    { nlinarith [cos_sq x, pow_two_nonneg x]},
  rw mul_self_le_mul_self_iff _ (cosh_nonneg x),
  { rw [one_mul, ← pow_two],
    exact G},
  { norm_num},
end

private lemma aux_lemma (x : ℝ) (h : 1 ≤ x) : 1 / (x + sqrt (x ^ 2 - 1)) = x - sqrt (x ^ 2 - 1) :=
begin
  refine (eq_one_div_of_mul_eq_one _).symm,
  rw [add_mul, mul_sub, mul_sub, ← pow_two, ← pow_two, sqr_sqrt],
  {ring},
  { rw [le_sub_iff_add_le, zero_add],
    rw mul_self_le_mul_self_iff at h,
    { rw [one_mul, ← pow_two] at h,
      exact h},
    { norm_num},
    { linarith},
  }
end

private lemma x_sq_sub_one_pos (x : ℝ) (h : 1 ≤ x): 0 ≤ x ^ 2 - 1 :=
begin
  rw [le_sub, sub_zero], 
  rw mul_self_le_mul_self_iff _ _ at h,
  { rw [one_mul, ← pow_two] at h,
    exact h},
  { norm_num},
  { exact h' x h},
end

private lemma b_lt_sqrt_b_one_add_sq (b : ℝ) (h : 1 ≤ b) : sqrt (b ^ 2 - 1) < b :=
begin
  have H : b ^ 2 - 1 < b ^ 2,
  { linarith},
  rw [mul_self_lt_mul_self_iff (sqrt_nonneg (b ^ 2 - 1)) (h' b h), ← pow_two, ← pow_two, sqr_sqrt], 
  { linarith},
  { exact x_sq_sub_one_pos b h}
end

lemma cosh_strict_mono (x : ℝ) (h : 0 ≤ x) : strict_mono cosh :=
strict_mono_of_deriv_pos differentiable_cosh (by rw [real.deriv_cosh];
begin
  intros x,
  sorry
end
)


lemma cosh_injective : function.injective cosh :=
begin
  sorry
end

lemma cosh_arcosh (x : ℝ) (h : 1 ≤ x) : cosh (arcosh x) = x :=
begin
  rw [cosh_eq, arcosh_eq, exp_log, ← log_inv, exp_log, ← one_div, aux_lemma x h],
  { ring},
  rw [← one_div, aux_lemma x h],
  { rw [lt_sub_iff_add_lt, zero_add, mul_self_lt_mul_self_iff (sqrt_nonneg (x ^ 2 - 1)) (h' x h)],
    rw [← pow_two, ← pow_two, sqr_sqrt],
    { linarith},
    { exact x_sq_sub_one_pos x h}},
  { apply lt_add_of_lt_of_nonneg,
    { linarith},
    { exact sqrt_nonneg (x ^ 2 - 1)}},
end

lemma arcosh_cosh (x : ℝ) (h : 1 ≤ x) : arcosh (cosh x) = x :=
function.right_inverse_of_injective_of_left_inverse cosh_injective cosh_arcosh x

