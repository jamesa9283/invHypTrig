import data.real.basic data.complex.exponential

/-- The real definition of `sinh`-/
lemma sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
by {simp only [sinh, complex.sinh, complex.div_re, complex.exp_of_real_re, complex.one_re,
  bit0_zero, add_zero, complex.sub_re, euclidean_domain.zero_div, complex.bit0_re,
  complex.one_im, complex.bit0_im, mul_zero, ← complex.of_real_neg, complex.norm_sq],
  ring}