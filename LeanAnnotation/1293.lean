import Mathlib

/-!

If $G_1$ acts freely on $E_1$ and $G_2$ acts freely on $E_2$, then $G_1 \times G_2$ acts
freely on $E_1 \times E_2$.

**Proof:** Suppose $(g_1, g_2) \in G_1 \times G_2$ fixes $(e_1, e_2) \in E_1 \times E_2$.
Then $(g_1, g_2) \cdot (e_1, e_2) = (e_1, e_2)$, which means
$(g_1 \cdot e_1, g_2 \cdot e_2) = (e_1, e_2)$ by the componentwise product action.
Therefore $g_1 \cdot e_1 = e_1$ and $g_2 \cdot e_2 = e_2$. Since both actions are free,
$g_1 = 1_{G_1}$ and $g_2 = 1_{G_2}$, so $(g_1, g_2) = (1_{G_1}, 1_{G_2})$.
-/

/--
A group action is called free if the only group element that fixes some point is the identity.
-/
def FreeAction (G : Type*) [Group G] (X : Type*) [MulAction G X] : Prop :=
  ∀ g : G, (∃ x : X, g • x = x) → g = 1

/--
The product action of two monoids on the product of two spaces.
Given monoids M and N acting on spaces α and β respectively, we define how the product
monoid M × N acts on the product space α × β. The action is defined componentwise:
(m, n) • (a, b) = (m • a, n • b).
-/
instance mulAction_of_prod_prod {M N α β : Type*} [Monoid M] [Monoid N]
    [MulAction M α] [MulAction N β] : MulAction (M × N) (α × β) where
  smul := by
    rintro ⟨m, n⟩ ⟨a, b⟩
    exact ⟨m • a, n • b⟩
  mul_smul _ _ _ := by ext <;> exact mul_smul ..
  one_smul _ := by ext <;> exact one_smul ..

/-- Simplification lemma for the product action. -/
@[simp]
lemma prod_smul {M N α β : Type*} [Monoid M] [Monoid N] [MulAction M α] [MulAction N β]
    (m : M) (n : N) (a : α) (b : β) :
    (m, n) • (a, b) = (m • a, n • b) := rfl

/--
If G₁ acts freely on E₁ and G₂ acts freely on E₂, then the product group G₁ × G₂
acts freely on the product space E₁ × E₂ using the componentwise product action.
-/
theorem prod_prod_free_action (G₁ G₂ : Type*) [Group G₁] [Group G₂]
    (E₁ E₂ : Type*) [MulAction G₁ E₁] [MulAction G₂ E₂]
    (hfa₁ : FreeAction G₁ E₁) (hfa₂ : FreeAction G₂ E₂) :
    FreeAction (G₁ × G₂) (E₁ × E₂) := by
  -- assume (g₁, g₂) fixes some point (e₁, e₂)
  intro ⟨g₁, g₂⟩ ⟨⟨e₁, e₂⟩, h⟩
  simp only [prod_smul, Prod.mk.injEq] at h
  rcases h with ⟨h₁, h₂⟩
  -- since g₁ fixes e₁, we have g₁ = 1
  specialize hfa₁ g₁ (by use e₁)
  -- since g₂ fixes e₂, we have g₂ = 1
  specialize hfa₂ g₂ (by use e₂)
  -- Conclude that (g₁, g₂) = (1, 1)
  simp [hfa₁, hfa₂]
