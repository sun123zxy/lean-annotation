import Mathlib

/--
If `R` is a non-unital ring and `a ∈ R` is nonzero with `a⁴ + a = 2a³`,
then `R` contains a nonzero idempotent element.
-/
theorem exists_nonzero_idempotent_of_a_pow_eq (R : Type*) [NonUnitalRing R]
    (a : R) (ha_nonzero : a ≠ 0) (h_eq : a * a * a * a + a = a * a * a + a * a * a) :
    ∃ x : R, x ≠ 0 ∧ x * x = x := by
  -- Construct candidate idempotent e = a² - a
  set e := a * a - a with he_def
  -- Prove e is idempotent using the given equation
  have he_idem : e * e = e := by
    rw [he_def]
    repeat rw [sub_mul]
    repeat rw [mul_sub]
    repeat rw [← mul_assoc]
    repeat rw [← sub_add]
    apply_fun fun t => -a + t at h_eq
    rw [add_comm] at h_eq
    simp at h_eq
    rw [h_eq]
    simp [add_sub_assoc]
    rw [add_comm, sub_eq_add_neg]
  -- Case analysis: either e ≠ 0 or e = 0
  by_cases h : e = 0
  · -- Case 1: e = 0, so a² = a (a is idempotent)
    use a
    constructor
    · assumption
    · rw [h] at he_def
      apply_fun (fun t => t + a) at he_def
      simp only [zero_add, sub_add_cancel] at he_def
      exact he_def.symm
  · --- Case 2: e ≠ 0, so e is our nonzero idempotent
    use e
