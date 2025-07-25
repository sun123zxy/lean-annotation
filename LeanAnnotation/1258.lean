import Mathlib

variable (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P] [Module.Free R P]

/--
Every surjective linear map onto a free module splits.
-/
theorem free_split (M : Type*) [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] P) (surj_f : Function.Surjective f) :
    ∃ (g : P →ₗ[R] M), LinearMap.comp f g = LinearMap.id := by
  -- Free modules are projective. Use the projective lifting property to find a split map.
  exact Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) surj_f
