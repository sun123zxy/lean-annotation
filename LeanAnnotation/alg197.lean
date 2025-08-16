import Mathlib

open PowerSeries

/-- we use the formal power series over ℝ -/
abbrev O := ℝ⟦X⟧

/-- O is not ℝ itself -/
lemma algebra_R_O_proper : ∃ f : O, f ∉ (algebraMap ℝ O).range := by
  simp
  by_contra! h
  rcases h X with ⟨x, hx⟩
  apply_fun coeff ℝ 1 at hx
  simp only [coeff_succ_C, coeff_one_X, zero_ne_one] at hx

/-- there is no square root of -1 in O -/
lemma O_has_no_square_root_of_neg_one : ¬ (∃ (f : O), f^2 = -1) := by
  rintro ⟨f, hf⟩
  -- focus on the constant term
  apply_fun (constantCoeff ℝ) at hf
  simp only [map_pow, map_neg, constantCoeff_one] at hf
  linarith [sq_nonneg ((constantCoeff ℝ) f)]

/-- no ℂ-algebra structure on O, i.e. ℂ ⊈ O -/
lemma no_algebra_C_O [Algebra ℂ O] : False := by
  apply O_has_no_square_root_of_neg_one
  use (algebraMap ℂ O) (Complex.I)
  rw [← RingHom.map_pow]
  simp only [Complex.I_sq, map_neg, map_one]

/--
there exists a local commutative ring O with an ℝ-algebra structure s.t.
it is not ℝ itself and admits no ℂ-algebra structure
-/
theorem epic : ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℝ O) (_ : IsLocalRing O)
    (_ : Function.Injective (algebraMap ℝ O)) (_ : ∃ f : O, f ∉ (algebraMap ℝ O).range),
    [Algebra ℂ O] → False := by
  use O
  use inferInstance
  use inferInstance
  use inferInstance
  use (algebraMap ℝ O).injective
  use algebra_R_O_proper
  exact no_algebra_C_O
