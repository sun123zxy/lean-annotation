import Mathlib

namespace Submodule

#check Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
#check TwoSidedIdeal.mem_jacobson_iff

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (I : Ideal R) (N : Submodule R M)

theorem nakayama' (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (hin : N ≤ I • N) : N = ⊥ := by
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin with ⟨r, ⟨hr, hn⟩⟩
  replace hr : r ∈ Ideal.jacobson ⊥ := by
    sorry
  #check TwoSidedIdeal.mem_jacobson_iff.mp hr
  rw [TwoSidedIdeal.mem_jacobson_iff] at hr
  sorry

theorem nakayama'' (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (P : Submodule R M) (hp : P ≤ N) (hnp : N ≤ I • N + P) : P = N := by
  sorry

theorem nakayama''' (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (t : Set N) (ht : Submodule.span R (Quotient.mk '' t : Set (N ⧸ I • (⊤ : Submodule R N))) = ⊤) : Submodule.span R t = ⊤ := by
  sorry

end Submodule

namespace CotangentDim

variable (A : Type*) [CommRing A] [IsLocalRing A]

local notation "m" => IsLocalRing.maximalIdeal A
local notation "cot" => IsLocalRing.CotangentSpace A
local notation "k" => IsLocalRing.ResidueField A

open Cardinal

theorem cotangent_dim (hm : Submodule.FG m) (d : ℕ) (b : Basis (Fin d) k cot) :
    ∃ S : Finset m, (S.card = d) ∧ Submodule.span A (S : Set m) = ⊤ := by
  haveI : ∃ T : Set cot, Submodule.span k T = ⊤ := by
    use Set.range b
    exact Basis.span_eq b
  rcases this with ⟨T, hT⟩

  sorry
end CotangentDim
