import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B]

/-- If every prime ideal of `A` is the contraction of some prime ideal of `B`
(along `f`), then the induced map is surjective. -/
theorem comap_surjective_of_all_primes_contracted
    (f : A →+* B)
    (h : ∀ P : PrimeSpectrum A, ∃ Q : PrimeSpectrum B, PrimeSpectrum.comap f Q = P) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  /- This is by definition. -/
  assumption
