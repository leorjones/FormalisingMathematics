import Mathlib

/-# Sylow Theorems yay-/

/- # Preliminaries -/
variable (p : ℕ) (G H : Type*) [Group G] {H : Subgroup G} {pCond : p.Prime}
variable {p} {G}

open BigOperators MulAction

instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _


lemma conj_class [Fintype G] [Fintype <| ConjClasses G] [∀ x : ConjClasses G, Fintype x.carrier] :
Fintype.card G = ∑ x : ConjClasses G, x.carrier.toFinset.card := by sorry

lemma normaliser (P : Sylow p G) (Q : Subgroup G) (h : IsPGroup p Q) : Q ≤ P.normalizer → Q ≤ P := by sorry

variable [MulAction G X] (x : X)
theorem orbit_stabiliser [Fintype G] [∀ x : X, Fintype <| stabilizer G x] [∀ x : X, Fintype (orbit G x)]:
Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (orbit G x) := by sorry


/- # Sylow I
Existence of Sylow p-groups
|G| = pᵃm (p ∤ m) → G has a subgroup of order pᵃ -/

theorem SylowI (a m : ℕ) [Fintype G] [Fintype H] (h :¬ (p ∣ m)): Fintype.card G = p^a * m  → Fintype.card H = p^a:= by
  sorry

/- # Sylow II
Number of Sylow p-groups
nₚ(G) ≡ 1 % p -/

local notation "Φ" => Quotient <| orbitRel G (Sylow p G)

lemma orbit_div_G  :   := by sorry

theorem SylowII [Fintype (Sylow p G)]: Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  have P : Sylow p G := by sorry
  have h : fixedPoints P (Sylow p G) = {P} := by sorry
  have _ : Fintype (fixedPoints P (Sylow p G)) := by
    rw[h]
    infer_instance
  have h2 : Fintype.card (fixedPoints P (Sylow p G)) = 1 := by simp [h]
  have h3 (Q : Sylow p G)[Fintype (fixedPoints Q (Sylow p G))]: Fintype.card (fixedPoints Q (Sylow p G)) = 1 → P = Q := by sorry
  have h4 (R : orbit (Sylow p G) p):
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

theorem SylowIV [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) := by
  sorry
