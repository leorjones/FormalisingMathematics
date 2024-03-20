import Mathlib

/-# Sylow Theorems yay-/

/- # Preliminaries -/
variable (p : ℕ) (G H : Type*) [Group G] {H : Subgroup G} {pCond : Fact p.Prime}
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

lemma orbit_div_G [Fintype G] [∀ x : X, Fintype (orbit G x)] (y : X): Fintype.card (orbit G y) ∣ Fintype.card G  := by sorry


-- lemma orbit_one : :=
--   have P : Sylow p G := by sorry
--   have h : fixedPoints P (Sylow p G) = {P} := by sorry
--   have _ : Fintype (fixedPoints P (Sylow p G)) := by
--     rw[h]
--     infer_instance
--   have h2 : Fintype.card (fixedPoints P (Sylow p G)) = 1 := by simp [h]

open Fintype

theorem SylowII [Fintype (Sylow p G)](P : Sylow p G)(y : Sylow p G)[∀ x : Sylow p G, Fintype (orbit P x)]: Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  -- have P : Sylow p G := by sorry
  have h : fixedPoints P (Sylow p G) = {P} := by sorry
  have _ : Fintype (fixedPoints P (Sylow p G)) := by
    rw[h]
    infer_instance
  have h2 : Fintype.card (fixedPoints P (Sylow p G)) = 1 := by simp [h]
  have h3 : Fintype.card (orbit P y) = 1 → (orbit P y) = {P} := by sorry
  have h4 [Fintype P]: Fintype.card (orbit P y) ∣  Fintype.card P := by
    apply orbit_div_G
  have h5 [Fintype P][Fintype G] : p ∣ Fintype.card P := by
    simp[Nat.instDvdNat]
    obtain ⟨n, heq : card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
    -- cases n
    -- rw [heq]
    -- simp
    use p ^ (n-1)
    rw[heq]
    ring_nf
    sorry
  have h6 : Fintype.card (orbit P y) ≠ 1 → p ∣ Fintype.card (orbit P y) := by sorry

  sorry

/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/

variable [Fintype (Sylow p G)][MulAction H (Sylow p G)][∀ q : Sylow p G, Fintype (orbit H q)]
theorem SylowIII (h : IsPGroup p H) : ∃ Q : Sylow p G, H ≤ Q := by
  have h1 : ∃ q : Sylow p G, Fintype.card (orbit H q) = 1 := by sorry -- Sylow II
  cases' h1 with q h1
  have h2 : H ≤ q.normalizer := by sorry
  use q
  apply normaliser
  exact h
  exact h2

/- # Sylow IV
Sylₚ(G) is a single conjugacy class
∀ Q, P ∈ Sylₚ(G), ∃ g s.t Q = ᵍP -/

theorem SylowIV [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) := by
  sorry
