import Mathlib

/-!
Let $p$ be an odd prime and $t$ a positive integer.
Suppose $r$ is an even integer that is a primitive root modulo $p^t$.
Prove that $r + p^t$ is a primitive root modulo $2p^t$.

Our strategy is as follows:

- Show that $\varphi(p^t) = \varphi(2 p^t)$.

- Show that the order of $r + p^t$ is divided by $\varphi(p^t) = \varphi(2 p^t)$. In fact,
  $$
  (r + p^t)^\alpha \equiv 1 \pmod{2 p^t}
  $$
  implies
  $$
  (r + p^t)^\alpha \equiv 1 \pmod{p^t}
  $$
  which is equivalent to
  $$
  r^\alpha \equiv 1 \pmod{p^t}
  $$

- The order of $r + p^t$ divides $\varphi(2 p^t)$, because it is the order
  of the whole multiplicative group.

- Confirm the order of $r + p^t$ is exactly $\varphi(2 p^t)$ by divisibility.

- Use the definition of the primitive root to conclude.
-/

open Nat

theorem primitive_root (p : ℕ) (t : ℕ) (r : ℤ)
    (hp : Nat.Prime p)
    (hp_odd : Odd p)
    (ht : 0 < t)
    (hr_even : Even r)
    (hr_prim : orderOf (r : ZMod (p ^ t)) = φ (p ^ t)) :
    orderOf (r + p ^ t : ZMod (2 * p ^ t)) = φ (2 * p ^ t) := by

  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  haveI : IsUnit (r : ZMod (p ^ t)) := by sorry
  obtain ⟨ur, h_ur⟩ := this
  rw [← h_ur, orderOf_units] at hr_prim

  haveI : IsUnit (r + p ^ t : ZMod (2 * p ^ t)) := by sorry
  obtain ⟨urpt, h_urpt⟩ := this
  rw [← h_urpt, orderOf_units]


  have totient_eq : φ (2 * p ^ t) = φ (p ^ t) := by
    sorry

  -- Show the equality by divisibility
  apply Nat.dvd_antisymm
  · rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  · rw [totient_eq]
    rw [← hr_prim]

    -- Show that orderOf ur divides orderOf urpt
    rw [orderOf_dvd_iff_pow_eq_one]
    sorry
