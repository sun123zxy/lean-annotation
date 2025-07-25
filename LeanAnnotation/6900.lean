import Mathlib

/-!
Let $p$ be an odd prime and $t$ a positive integer.
Suppose $r$ is an even integer that is a primitive root modulo $p^t$.
Prove that $r + p^t$ is a primitive root modulo $2p^t$.

Our strategy is as follows:

- Show that $\varphi(p^t) = \varphi(2 p^t)$.

- Show that the order of $r + p^t$ modulo $2 p^t$ is divided by $\varphi(p^t) = \varphi(2 p^t)$.
  In fact, take $\alpha$ be the order of $r + p^t$ modulo $2 p^t$, we have
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

theorem rpt_primitive_root (p : ℕ) (t : ℕ) (r : ℤ)
    (hp : Nat.Prime p)
    (hp_odd : Odd p)
    (ht : 0 < t)
    (hr_even : Even r)
    (hr_prim : orderOf (r : ZMod (p ^ t)) = φ (p ^ t)) :
    orderOf (r + p ^ t : ZMod (2 * p ^ t)) = φ (2 * p ^ t) := by

  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  have totient_eq : φ (2 * p ^ t) = φ (p ^ t) := by
    sorry

  haveI : IsUnit (r : ZMod (p ^ t)) := by
    apply IsOfFinOrder.isUnit
    rw [← orderOf_pos_iff]
    rw [hr_prim]
    exact pos_of_neZero (φ (p ^ t))
  obtain ⟨ur, h_ur⟩ := this
  rw [← h_ur, orderOf_units] at hr_prim

  haveI : IsUnit (r + p ^ t : ZMod (2 * p ^ t)) := by
    norm_cast
    rw [ZMod.isUnit_iff_coprime]
    rw [coprime_iff_gcd_eq_one]
    lift p to PNat using pos_of_neZero p
    norm_cast
    rw [← PNat.gcd_coe]
    #check PNat.gcd
    #check PNat.Coprime.gcd_mul
    rw [PNat.Coprime.gcd_mul]
    -- show that gcd(p^t, r+p^t) = 1


  obtain ⟨urpt, h_urpt⟩ := this
  rw [← h_urpt, orderOf_units]

  -- Show the equality by divisibility
  apply Nat.dvd_antisymm
  · -- Direction 1: $\mathrm{ord}_{2p^t}(r + p^t) \mid \varphi(2p^t)$ by Lagrange's theorem
    rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  · -- Direction 2: $\varphi(p^t) = \mathrm{ord}_{p^t}(r) \mid \mathrm{ord}_{2p^t}(r + p^t)$
    rw [totient_eq]
    rw [← hr_prim]
    -- Use $(r + p^t)^{\mathrm{ord}_{2p^t}(r + p^t)} = 1$ in $\mathbb{Z}/2p^t\mathbb{Z}$
    haveI := pow_orderOf_eq_one urpt
    -- Reduce to modulo $p^t$
    apply_fun (fun x => x.val.val % (p ^ t)) at this
    simp [ZMod.val_one_eq_one_mod] at this
    rw [h_urpt] at this
    rw [← ZMod.natCast_eq_natCast_iff'] at this
    simp only [ZMod.natCast_val, dvd_mul_left, ZMod.cast_pow, ZMod.cast_add, ZMod.cast_intCast,
      ZMod.cast_natCast, cast_one] at this
    -- use $p^t \equiv 0 \pmod{p^t}$ to simplify
    conv at this => lhs; lhs; rhs; tactic => norm_cast
    simp only [CharP.cast_eq_zero, add_zero] at this
    -- Therefore $\mathrm{ord}_{p^t}(r) \mid \mathrm{ord}_{2p^t}(r + p^t)$
    rw [← h_ur] at this
    rw [orderOf_dvd_iff_pow_eq_one]
    apply_fun Units.val
    · simp [this]
    · exact Units.val_injective
