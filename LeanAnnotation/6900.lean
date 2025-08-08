import Mathlib

namespace ZMod
theorem coe_int_isUnit_iff_isCoprime (n : ℤ) (m : ℕ) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : ℤ) n := by
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_comm, ← isUnit_iff_coprime, Associated.isUnit_iff]
  simpa only [eq_intCast, Int.cast_natCast] using (Int.associated_natAbs _).map (Int.castRingHom _)
end ZMod

namespace Nat
theorem gcd_right_eq_iff {m n n' : Nat} : gcd m n = gcd m n' ↔ ∀ k, k ∣ m → (k ∣ n ↔ k ∣ n') := by
  refine ⟨fun h k hkm => ⟨fun hkn => ?_, fun hkn' => ?_⟩, fun h => Nat.dvd_antisymm ?_ ?_⟩
  · exact Nat.dvd_trans (h ▸ dvd_gcd hkm hkn) (Nat.gcd_dvd_right m n')
  · exact Nat.dvd_trans (h ▸ dvd_gcd hkm hkn') (Nat.gcd_dvd_right m n)
  · exact dvd_gcd_iff.2 ⟨gcd_dvd_left _ _, (h _ (gcd_dvd_left _ _)).1 (gcd_dvd_right _ _)⟩
  · exact dvd_gcd_iff.2 ⟨gcd_dvd_left _ _, (h _ (gcd_dvd_left _ _)).2 (gcd_dvd_right _ _)⟩
end Nat

namespace Int
@[simp] protected theorem dvd_add_mul_self {a b c : Int} : a ∣ b + c * a ↔ a ∣ b := by
  rw [Int.dvd_add_left (Int.dvd_mul_left c a)]
@[simp] protected theorem dvd_add_self_mul {a b c : Int} : a ∣ b + a * c ↔ a ∣ b := by
  rw [Int.mul_comm, Int.dvd_add_mul_self]
theorem gcd_eq_natAbs_gcd_natAbs (m n : Int) : gcd m n = Nat.gcd m.natAbs n.natAbs := rfl
theorem gcd_right_eq_iff {a b b' : Int} : gcd a b = gcd a b' ↔ ∀ c, c ∣ a → (c ∣ b ↔ c ∣ b') := by
  simp only [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_right_eq_iff]
  refine ⟨fun hk c hc => ?_, fun hc k hk => ?_⟩
  · simpa using hk c.natAbs (by simpa)
  · simpa [ofNat_dvd_left] using hc k (by simpa [ofNat_dvd_left])
@[simp] theorem gcd_add_mul_right_right (m n k : Int) : gcd m (n + k * m) = gcd m n :=
  gcd_right_eq_iff.2 (by rintro c ⟨l, rfl⟩; rw [Int.mul_comm, Int.mul_assoc, Int.dvd_add_self_mul])
@[simp] theorem gcd_add_mul_right_left (m n k : Int) : gcd (n + k * m) m = gcd n m := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]
@[simp] theorem gcd_add_self_left (m n : Int) : gcd (n + m) m = gcd n m := by
  simpa using gcd_add_mul_right_left _ _ 1

@[simp] theorem gcd_add_mul_left_left (m n k : Int) : gcd (n + m * k) m = gcd n m := by
  rw [Int.mul_comm, gcd_add_mul_right_left]
@[simp] theorem gcd_mul_left_add_left (m n k : Int) : gcd (m * k + n) m = gcd n m := by
  rw [Int.add_comm, gcd_add_mul_left_left]
@[simp] theorem gcd_add_left_left_of_dvd {m k : Int} (n : Int) :
    m ∣ k → gcd (k + n) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_add_left m n l

theorem dvd_coe_gcd {a b c : Int} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (gcd a b : Int) :=
  ofNat_dvd_right.2 (Nat.dvd_gcd (natAbs_dvd_natAbs.2 ha) (natAbs_dvd_natAbs.2 hb))
theorem dvd_gcd' {a b : Int} {c : Nat} (ha : (c : Int) ∣ a) (hb : (c : Int) ∣ b) : c ∣ gcd a b :=
  ofNat_dvd.1 (dvd_coe_gcd ha hb)
theorem gcd_eq_iff {a b : Int} {g : Nat} :
    gcd a b = g ↔ (g : Int) ∣ a ∧ (g : Int) ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  refine ⟨?_, fun ⟨ha, hb, hc⟩ => Nat.dvd_antisymm ?_ (dvd_gcd ha hb)⟩
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Int.dvd_coe_gcd⟩
  · exact Int.ofNat_dvd.1 (hc _ (gcd_dvd_left _ _) (gcd_dvd_right _ _))
end Int

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
      simp only [dvd_mul_right, Int.gcd_add_left_left_of_dvd, Int.one_gcd]
    -- Which follows from the fact we've shown previously that $r$ is a unit modulo $p^t$
    haveI : Int.gcd (r + p ^ t) (p ^ t) = 1 := by
      simp only [Int.gcd_add_self_left]
      norm_cast
      rw [Int.gcd_comm, ← Int.isCoprime_iff_gcd_eq_one, ← ZMod.coe_int_isUnit_iff_isCoprime]
      exact isUnit_r
    rw [Int.gcd_eq_iff] at this
    simp only [cast_one, isUnit_one, IsUnit.dvd, true_and] at this
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


    conv at this => lhs; congr; lhs; rhs; tactic => norm_cast

    simp only [CharP.cast_eq_zero, add_zero] at this
    -- Therefore $\mathrm{ord}_{p^t}(r) \mid \mathrm{ord}_{2p^t}(r + p^t)$
    rw [← h_ur] at this
    rw [orderOf_dvd_iff_pow_eq_one]
    apply_fun Units.val
    · simp [this]
    · apply Units.ext
