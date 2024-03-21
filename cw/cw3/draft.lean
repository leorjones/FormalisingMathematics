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

theorem SylowI (a m : ℕ) [Fintype G] [Fintype H] (h :¬ (p ∣ m)): Fintype.card G = p ^ a * m  → Fintype.card H = p^a:= by
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

lemma number_theory (a p n : ℕ ) (h: a ∣ p ^ n) (h2 : a ≠ 1) (h3 : Fact p.Prime) : (p ∣ a) := by
  simp[Nat.instDvdNat]
  cases' n with n
  simp at h
  by_contra
  apply h2
  exact h
  simp[Nat.pow_succ'] at h

  simp[Nat.instDvdNat] at h

  sorry -- ASK


theorem SylowII [Fintype (Sylow p G)](P : Sylow p G)[Fintype P](y : Sylow p G)[∀ x : Sylow p G, Fintype (orbit P x)]: Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  -- have P : Sylow p G := by sorry
  have h : fixedPoints P (Sylow p G) = {P} := by sorry
  have _ : Fintype (fixedPoints P (Sylow p G)) := by
    rw[h]
    infer_instance
  have h2 : card (fixedPoints P (Sylow p G)) = 1 := by simp [h]
  have h3 : card (orbit P y) = 1 → (orbit P y) = {P} := by sorry
  have h4 : card (orbit P y) ∣  card P := by
    apply orbit_div_G
  have h5' [Fintype P] : ∃ n, card P = p ^ n := by
    obtain ⟨a, heq : card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
    use a
  cases' h5' with n h5''
  rw[h5''] at h4
  have h6 : card (orbit P y) ≠ 1 → p ∣ card (orbit P y) := by
    intro q
    apply number_theory (card (orbit P y)) p n
    exact h4
    exact q
    exact pCond
--- convert unique orbit order one + other orbits div by p to final form ASK
  sorry



/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/


lemma normal {g : G} {P : Sylow p G} : g • P = P ↔ g ∈ (P : Subgroup G).normalizer := Sylow.smul_eq_iff_mem_normalizer
variable [Fintype (Sylow p G)][MulAction H (Sylow p G)][∀ q : Sylow p G, Fintype (orbit H q)]

lemma orbit_def : y ∈ orbit G x → ∃ g : G, y = g • x := by
  simp[orbit]
  intros a h
  use a
  simp [h]


theorem SylowIII (h : IsPGroup p H)[∀ q : Sylow p G, Fintype (orbit H q)]: ∃ P : Sylow p G, H ≤ P := by
  have h1 : ∃ P : Sylow p G, Fintype.card (orbit H P) = 1 := by sorry -- Sylow II
  cases' h1 with P h1
  have h2 : P ∈ orbit H P := by apply mem_orbit_self
  rw [card_eq_one_iff] at h1
  have h3 : orbit H P = {P} := by sorry --- ASK
  have hn : H ≤ Subgroup.normalizer P := by
    rw[SetLike.le_def] --- die
    intros h h5
    --- have h : H := ⟨h, h5⟩
    rw [← normal]
    rw [orbit] at h3
    have hm : h • P ∈ orbit H P := by sorry --- ⟨h, rfl⟩
    -- ASK

    sorry
  use P
  apply normaliser
  exact h
  exact hn

/- # Sylow IV
Sylₚ(G) is a single conjugacy class
∀ Q, P ∈ Sylₚ(G), ∃ g s.t Q = ᵍP -/

theorem SylowIV [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) := by
  constructor
  intros P Q
  let Ω := {g • P | g : G}
  let x : Ω := by sorry
  let φ : MulAction Q Ω := by sorry
  have _ : ∀ x : Ω, Fintype (orbit Q x) := by sorry
  have _ : Fintype Ω := by sorry
  have h1 : card Ω ≡ 1 [MOD p] := by sorry --Sylow II
  have h2 : ∃ R : Ω, card (orbit Q R) = 1 := by sorry
  cases' h2 with R
  have h3 : orbit Q R = {R} := by sorry ---same as Sylow III
  have R : Subgroup G := by sorry
  have h4 : Q ≤ R.normalizer := by sorry --- same as Sylow III
  --- apply normaliser at h4


  sorry

-- theorem SylowIV [Finite (Sylow p G)](P : Sylow p G) : Sylow p G = {g • P | g : G} := by
--   sorry
