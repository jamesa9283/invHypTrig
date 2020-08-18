import data.complex.exponential data.real.basic
open real
noncomputable theory
variables (x a b c : ℝ)

def arsinh := ℝ → ℝ

#check arsinh 

def inverse_func := ∀ y,  f (g y) = y

lemma sinh_bijective : function.bijective (sinh) :=
begin
  unfold function.bijective function.injective function.surjective,
  split,
  {
    intros a b,
    sorry
  },
  {
      intros a,
      use (sinh a)⁻¹,
      sorry
  }
end


lemma comp_sq : a * x * x + b * x + c = 0 → a * (x - (b / 2*a)) * (x - (b / 2*a)) + c - b*b/4*a*a = 0 :=
begin
  intros fabc,
  sorry
end