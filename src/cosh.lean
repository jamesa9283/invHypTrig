import basic analysis.convex.extrema

open real
noncomputable theory

def arcosh (x : ℝ) := log (x + sqrt(x^2 - 1))

lemma half_le_cosh (x : ℝ)  (h : 0 ≤ x) : 1/2 ≤ cosh x :=
begin
    rw cosh_eq,
    apply div_le_div,
    {
      have H : 0 < exp x := (exp_pos x),
      have G : 0 < exp (-x) := (exp_pos (-x)),
      linarith,
    },
    {
      have H : 1 ≤ exp x := by {convert exp_monotone h, rw exp_zero},
      have G : 0 < exp (-x) := (exp_pos (-x)),
      linarith,
    },
    {
        norm_num
    },
    {
        norm_num
    }
end

