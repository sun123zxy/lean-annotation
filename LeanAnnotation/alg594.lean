import Mathlib

namespace Submodule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (I : Ideal R) (N : Submodule R M)

/-
`exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`
is the existing Nakayama's lemma in Mathlib
-/

/--
Atiyah--MacDonald proposition 2.6 (Nakayama's lemma for the Jacobson radical)

If I is an ideal contained in the Jacobson radical and N is a finitely generated
submodule such that N ≤ I • N, then N = 0.

Note that in Mathlib v4.17.0 there is already a noncommutative version of this
See PR #21451, `FG.eq_bot_of_le_jacobson_smul`
-/
theorem nakayama_jacobson (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (hin : N ≤ I • N) : N = ⊥ := by
  -- Apply the basic Nakayama lemma to get r • N = 0
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin with ⟨r, ⟨hr, hn⟩⟩
  -- Since I ⊆ Jacobson radical, r - 1 is in the Jacobson radical
  replace hr := hi hr
  -- Elements in Jacobson radical are characterized by 1 - (r - 1) s being units for all s
  rw [Ideal.mem_jacobson_iff] at hr
  -- Apply this characterization with s = 1 to obtain that r is a unit and hence N = r • N = 0
  specialize hr 1
  rcases hr with ⟨z, hz⟩
  ring_nf at hz
  rw [Ideal.mem_bot] at hz
  apply_fun fun t => t + 1 at hz
  rw [neg_add_cancel_comm, zero_add] at hz
  rw [Submodule.eq_bot_iff]
  intro n' hn'
  specialize hn n' hn'
  apply_fun fun t => z • t at hn
  rw [← smul_assoc, smul_eq_mul, hz, smul_zero, one_smul] at hn
  exact hn

/--
Atiyah--MacDonald corollary 2.7 (Nakayama's lemma with submodules).

If I is contained in the Jacobson radical, N is finitely generated, P is a
submodule of N, and N ≤ I • N + P, then P = N.
-/
theorem nakayama_jacobson' (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (P : Submodule R M) (hp : P ≤ N) (hnp : N ≤ I • N + P) : P = N := by
  -- Consider the quotient N/P and show it equals 0
  let NquotP := map (P.mkQ) N
  -- N/P is finitely generated since N is
  have h_NquotP_FG : NquotP.FG := by
    apply FG.map
    exact hn
  -- Apply the quotient map to the inequality N ≤ I • N + P
  apply_fun map P.mkQ at hnp
  on_goal 2 => apply map_mono
  simp only [add_eq_sup, map_sup, map_smul'', mkQ_map_self, bot_le, sup_of_le_left] at hnp
  -- This gives us N/P ≤ I • (N/P), so we can apply Nakayama conclude N/P = 0 or N = P
  haveI := nakayama_jacobson I NquotP hi h_NquotP_FG hnp
  rw [Submodule.eq_bot_iff] at this
  simp only [mem_map, mkQ_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Quotient.mk_eq_zero, NquotP] at this
  exact le_antisymm hp this

/--
Atiyah--MacDonald corollary 2.8 (Nakayama's lemma for generating sets).

If I is contained in the Jacobson radical, N is finitely generated, t is a
subset of N, and the span of t generates the same quotient N/(I • N) as N itself,
then t generates all of N.
-/
theorem nakayama_jacobson'' (hi : I ≤ Ideal.jacobson ⊥) (hn : N.FG)
    (t : Set M) (htn : t ⊆ N) (hts : map (I • N).mkQ (span R t) = map (I • N).mkQ N) :
    span R t = N := by
  -- Let P = span R t for convenience
  let P := span R t; rw [(show span R t = P by rfl)] at *
  -- We have P ⊆ N since t ⊆ N
  have P_le_N : P ≤ N := by
    rw [span_le]
    exact htn
  -- Apply the previous corollary
  apply nakayama_jacobson' I N hi hn P P_le_N
  -- show N ≤ I • N + P from the quotient condition
  apply_fun comap (I • N).mkQ at hts
  simp only [comap_map_mkQ, comap_top, ← add_eq_sup] at hts
  rw [hts]
  simp only [add_eq_sup, le_sup_right]

end Submodule

namespace CotangentDim

variable (A : Type) [CommRing A] [IsLocalRing A]

local notation "m" => IsLocalRing.maximalIdeal A

open Submodule

/--
In a commutative local ring A, if the maximal ideal is finitely generated,
and a subset t of the maximal ideal generates m / m²,
then t generates the entire maximal ideal.

Although its probably better to work with
`Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)` directly,
this formulation avoids annoying isomorphisms and tricky inductions on quotients.
-/
theorem cotangent_span (hm : FG m)(t : Set A) (htm : t ⊆ m)
    (hts : map (m ^ 2).mkQ (span A t) = map (m ^ 2).mkQ m) : span A t = m := by
  -- Apply Nakayama for generating sets with I = m and N = m
  apply nakayama_jacobson'' m m (by apply IsLocalRing.maximalIdeal_le_jacobson) hm t htm
  -- Convert m • m to m² using the fact that smul equals multiplication for ideals
  rw [smul_eq_mul, ← pow_two]
  exact hts

/-
TODO: We've been a little dishonest here. Induction API does not work on a set of quotients.
Don't know how to handle this. Finset?
-/

local notation "cot" => IsLocalRing.CotangentSpace A
local notation "k" => IsLocalRing.ResidueField A

/- Ideally we should prove this -/
theorem cotangent_dim (hm : FG m) (d : ℕ) (hcotd : Module.finrank k cot = d) :
    ∃ s : Finset A, (s : Set A) ⊆ m ∧ (s.card = d) ∧ Ideal.span s = m := by sorry

/- I don't know if this is true -/
theorem set_ind {α : Type u} {s : Setoid α} {motive : Set (Quotient s) → Prop} :
    ((a : Set α) → motive (Quotient.mk s '' a)) → (q : Set (Quotient s)) → motive q :=
  sorry

end CotangentDim
