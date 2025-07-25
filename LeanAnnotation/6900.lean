import Mathlib

/-!
Let $p$ be an odd prime and $t$ a positive integer.
Suppose $r$ is an even integer that is a primitive root modulo $p^t$.
Prove that $r + p^t$ is a primitive root modulo $2p^t$.

Our proof goes as follows:

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

/--
If $r$ is an even primitive root modulo $p^t$ where $p$ is odd prime,
then $r + p^t$ is a primitive root modulo $2 p^t$.
-/
theorem rpt_primitive_root (p : ℕ) (t : ℕ) (r : ℤ)
    (hp : Nat.Prime p)
    (hp_odd : Odd p)
    (hr_even : Even r)
    (hr_prim : orderOf (r : ZMod (p ^ t)) = φ (p ^ t)) :
    orderOf (r + p ^ t : ZMod (2 * p ^ t)) = φ (2 * p ^ t) := by

  haveI : Nat.Prime 2 := by decide
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Odd (p ^ t) := Odd.pow hp_odd
  -- Since $r$ is even and $p^t$ is odd, $r + p^t$ is odd
  have odd_rpt : Odd (r + p ^ t) := by
    rw [add_comm]
    refine Odd.add_even ?_ hr_even
    norm_cast
  -- $\varphi(2p^t) = \varphi(p^t)$ since $\gcd(2, p^t) = 1$
  have totient_eq : φ (2 * p ^ t) = φ (p ^ t) := by
    rw [Nat.totient_mul]
    · simp only [totient_two, one_mul]
    · apply Nat.Prime.coprime_pow_of_not_dvd
      · assumption
      · intro h
        haveI := le_of_dvd (by decide) h
        haveI := Nat.Prime.one_lt hp
        haveI : p = 2 := by linarith
        rw [this] at hp_odd
        absurd hp_odd
        simp
  -- $r$ is a unit in $\mathbb{Z}/p^t\mathbb{Z}$ since it's a primitive root
  have isUnit_r : IsUnit (r : ZMod (p ^ t)) := by
    apply IsOfFinOrder.isUnit
    rw [← orderOf_pos_iff]
    rw [hr_prim]
    exact pos_of_neZero (φ (p ^ t))
  let ⟨ur, h_ur⟩ := isUnit_r
  rw [← h_ur, orderOf_units] at hr_prim

  -- Next we show that $r + p^t$ is a unit in $\mathbb{Z}/2p^t\mathbb{Z}$
  have isUnit_rpt : IsUnit (r + p ^ t : ZMod (2 * p ^ t)) := by
    norm_cast
    -- This is equivalent to $\gcd(r+p^t,2p^t)=1$
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    rw [Int.isCoprime_iff_gcd_eq_one]
    -- Apply the fact that $r+p^t$ is odd to reduce to show that $\gcd(r+p^t, p^t) = 1$
    rw [Int.gcd_eq_iff]
    simp only [cast_one, cast_mul, cast_ofNat, cast_pow, isUnit_one, IsUnit.dvd, true_and]
    intro c hc1 hc2
    have odd_c : Odd c := by
      rcases hc2 with ⟨d, hd⟩
      rw [hd, Int.odd_mul] at odd_rpt
      exact odd_rpt.left
    replace hc1 : c ∣ p ^ t := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one hc1
      rcases odd_c with ⟨c', hc'⟩
      rw [hc']
      simp
    -- Which follows from the fact we've shown previously that $r$ is a unit modulo $p^t$
    haveI : Int.gcd (r + p ^ t) (p ^ t) = 1 := by
      simp only [Int.gcd_add_self_left]
      norm_cast
      rw [Int.gcd_comm, ← Int.isCoprime_iff_gcd_eq_one, ← ZMod.coe_int_isUnit_iff_isCoprime]
      exact isUnit_r
    rw [Int.gcd_eq_iff] at this
    simp at this
    exact this c hc2 hc1
  let ⟨urpt, h_urpt⟩ := isUnit_rpt
  rw [← h_urpt, orderOf_units]

  -- Prove $\mathrm{ord}_{2p^t}(r + p^t) = \varphi(2p^t)$ by mutual divisibility
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
