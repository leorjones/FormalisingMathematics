import Mathlib

/-# Sylow Theorems yay-/

/- # Preliminaries -/
variable (p : ℕ) (G H : Type*) [Group G] {H : Subgroup G} {p_cond : p.Prime}
variable {p} {G}

instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

/- # Sylow I
Existence of Sylow p-groups
|G| = pᵃm (p ∤ m) → G has a subgroup of order pᵃ -/

theorem SylowI (a m : ℕ) [Fintype G] [Fintype H] (h :¬ (p ∣ m)): Fintype.card G = p^a * m  → Fintype.card H = p^a:= by
  sorry

/- # Sylow II
Number of Sylow p-groups
nₚ(G) ≡ 1 % p -/

theorem SylowII [Fintype (Sylow p G)]: Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  sorry

/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/

theorem SylowIII (h : IsPGroup p H) : ∃ Q : Sylow p G, H ≤ Q := by
  sorry

/- # Sylow IV
Sylₚ(G) is a single conjugacy class
∀ Q, P ∈ Sylₚ(G), ∃ g s.t Q = ᵍP -/

theorem SylowIV [Finite (Sylow p G)] : MulAction.IsPretransitive G (Sylow p G) := by
  sorry
