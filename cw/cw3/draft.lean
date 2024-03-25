import Mathlib

/-# Sylow Theorems yay-/

/- # Preliminaries -/
variable (p : ℕ) (G H : Type*) [Group G] {H J: Subgroup G} {pCond : Fact p.Prime}
variable {p} {G}

open BigOperators MulAction Fintype

instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _


lemma conj_class [Fintype G] [Fintype <| ConjClasses G] [∀ x : ConjClasses G, Fintype x.carrier] :
Fintype.card G = ∑ x : ConjClasses G, x.carrier.toFinset.card := by sorry

def φ (H J : Subgroup G) : (H × J) → G := fun g => g.1 * g.2

---example [Fintype P] [Fintype Q] [Fintype (P ⊓ Q).toSubgroup] (P Q : Subgroup G): Finset.inf (P ⊓ Q) id := by sorry

lemma normaliser (P : Sylow p G) (Q : Subgroup G) (h : IsPGroup p Q)/-[Fintype P][Fintype Q]-/:
Q ≤ P.normalizer → Q ≤ P := by
  --have (φ P Q).image : Subgroup G := by
  intro norm
  let PQ : Subgroup G := {
    carrier := Set.range (φ Q P)
    mul_mem' := by
      simp [φ]
      intros _ _ q1 hq1 p1 hp1 a q2 hq2 p2 hp2 b
      have h0 : q2⁻¹ ∈ P.normalizer := by
        rw [SetLike.le_def] at norm
        apply norm
        simp [inv_mem]
        exact hq2
      have h1 : (q2⁻¹ * p1 * q2) * p2 ∈ P := by
        apply mul_mem
        simp only [Subgroup.normalizer] at h0
        rw [h0] at hp1
        simp at hp1
        exact hp1
        exact hp2
      have h2 : q1 * q2 ∈ Q := by
        apply mul_mem
        exact hq1
        exact hq2
      use q1 * q2
      constructor
      exact h2
      use (q2⁻¹ * p1 * q2) * p2
      constructor
      exact h1
      rw [←a, ←b]
      simp [mul_assoc]
    one_mem' := by
      use 1
      simp [φ]
    inv_mem' := by
      simp [φ]
      intros a q hq p hp ha
      use q⁻¹
      constructor
      apply inv_mem
      exact hq
      use q * p⁻¹ * q⁻¹
      constructor
      have : q ∈ P.normalizer := by
        rw [SetLike.le_def] at norm
        apply norm
        exact hq
      simp only [Subgroup.normalizer] at this
      apply inv_mem at hp
      rw [this] at hp
      exact hp
      rw [← ha]
      simp [mul_assoc]
  }
  -- let unionPQ : Subgroup G := {
  --   carrier := (P.toSubgroup ⊓ Q)
  --   mul_mem':= sorry
  --   one_mem':= sorry
  --   inv_mem':= by sorry
  -- }
  -- have _ : Fintype PQ := by sorry
  -- have _ : Fintype unionPQ := by sorry
  -- have : card PQ = (card Q * card P) / card unionPQ := by sorry
  -- have _ : card PQ = card P * (unionPQ.relindex Q) := by sorry
  have h5 : IsPGroup p PQ := by sorry
  have h6 : P ≤ PQ := by
    rw [SetLike.le_def]
    intros a ha
    simp [φ]
    use 1
    constructor
    apply one_mem
    use a
    constructor
    exact ha
    apply one_mul
  have : PQ = P := by
    rcases P with ⟨a, b, c⟩
    apply c at h5
    apply h5 at h6
    exact h6
  have h7 : Q ≤ PQ := by
    rw [SetLike.le_def]
    intros a ha
    simp [φ]
    use a
    constructor
    exact ha
    use 1
    constructor
    apply one_mem
    apply mul_one
  rw [←this]
  exact h7

lemma normal {g : G} {P : Sylow p G} : g • P = P ↔ g ∈ (P : Subgroup G).normalizer := Sylow.smul_eq_iff_mem_normalizer

variable [MulAction G X] (x : X)
theorem orbit_stabiliser [Fintype G] [∀ x : X, Fintype <| stabilizer G x] [∀ x : X, Fintype (orbit G x)]:
Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (orbit G x) := by sorry


/- # Sylow I
Existence of Sylow p-groups
|G| = pᵃm (p ∤ m) → G has a subgroup of order pᵃ -/

theorem SylowI (a m : ℕ) [Fintype G] [Fintype H] (h :¬ (p ∣ m)): Fintype.card G = p ^ a * m  → Fintype.card H = p^a:= by
  sorry --- exists_subgroup_card_pow_prime

/- # Sylow II
Number of Sylow p-groups
nₚ(G) ≡ 1 % p -/

local notation "Φ" => Quotient <| orbitRel G (Sylow p G)

lemma orbit_div_G [Fintype G] [∀ x : X, Fintype (orbit G x)] (y : X): Fintype.card (orbit G y) ∣ Fintype.card G  := by sorry



lemma number_theory (a p n : ℕ ) (h: a ∣ p ^ n) (h2 : a ≠ 1) (h3 : Fact p.Prime) : (p ∣ a) := by
  --simp[Nat.instDvdNat]
  cases' n with n
  simp at h
  by_contra
  apply h2
  exact h
  rw [Nat.dvd_prime_pow] at h
  rcases h with ⟨k, ⟨_, hk'⟩⟩
  rw [hk']
  rw [Nat.dvd_prime_pow]
  use 1
  have : k ≠ 0 := by
    intro hk1
    rw [hk1] at hk'
    simp at hk'
    apply h2
    exact hk'
  constructor
  exact Nat.one_le_iff_ne_zero.mpr this
  simp
  simp [fact_iff] at h3
  exact h3
  simp [fact_iff] at h3
  exact h3


lemma card_stuff (X : Set S)(x : S)[Fintype X] (h : x ∈ X) (h1: card X = 1) : X = {x} := by
  ext a
  constructor
  · intro h2
    simp
    rw [card_eq_one_iff] at h1
    rcases h1 with ⟨⟨b, hb⟩ , hbp⟩
    have := hbp ⟨a, h2⟩
    simp at this
    rw[this]
    have := hbp ⟨x, h⟩
    simp at this
    rw [this]
  · intro h2
    simp at h2
    rw [h2]
    exact h


theorem SylowII [Fintype (Sylow p G)](P : Sylow p G)[Fintype P](Q : Sylow p G)[∀ x : Sylow p G, Fintype (orbit P x)]:
  Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  -- have P : Sylow p G := by sorry
  have h : fixedPoints P (Sylow p G) = {P} := by
    apply Set.ext
    intro Q
    have h2 : Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q.normalizer := by
      rw [SetLike.le_def]
      simp [normal]
    have h' : Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by
      rw[h2]
      constructor
      apply normaliser
      exact P.2
      have : Q ≤ Q.normalizer := Subgroup.le_normalizer
      intros a b c
      apply a at c
      apply this at c
      exact c
    have : P ≤ Q ↔ Q = P := by
      constructor
      intro hpq
      rw [Sylow.ext_iff, P.3 Q.2 hpq]
      exact fun a => Eq.le (id a.symm)
    rw [h', this]
    rfl
    ---simp [Sylow.ext_iff]
    --exact Set.ext fun (Q : Sylow p G) => ⟨sorry, sorry⟩

  have _ : Fintype (fixedPoints P (Sylow p G)) := by
    rw[h]
    infer_instance

  have h2 : card (fixedPoints P (Sylow p G)) = 1 := by simp [h]
  have h3 : card (orbit P Q) = 1 → (orbit P Q) = {P} := by
    rw [← mem_fixedPoints_iff_card_orbit_eq_one, ← h]
    intro h9
    have : Q ∈ orbit P Q := mem_orbit_self Q
    sorry
    --rw [card_eq_one_iff] at h2


    -- rw [card_eq_one_iff, ← h, fixedPoints]
    -- intro h9
    --rcases h2 with ⟨a, b⟩ --⟨⟨a, b⟩, c⟩
    -- have : Q ∈ orbit P Q := mem_orbit_self Q
    -- rw [h] at h9
    -- simp at h9

    ---apply b at this
  have h4 : card (orbit P Q) ∣  card P := by
    apply orbit_div_G
  have h5' [Fintype P] : ∃ n, card P = p ^ n := by
    obtain ⟨a, heq : card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
    use a
  cases' h5' with n h5''
  rw[h5''] at h4
  have h6 : card (orbit P Q) ≠ 1 → p ∣ card (orbit P Q) := by
    intro q
    apply number_theory (card (orbit P Q)) p n
    exact h4
    exact q
    exact pCond
--- convert unique orbit order one + other orbits div by p to final form ASK
  sorry



/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/


variable [Fintype (Sylow p G)][MulAction H (Sylow p G)][∀ q : Sylow p G, Fintype (orbit H q)]

lemma orbit_def : y ∈ orbit G x → ∃ g : G, y = g • x := by
  simp[orbit]
  intros a h
  use a
  simp [h]


theorem SylowIII (h : IsPGroup p H)[∀ q : Sylow p G, Fintype (orbit H q)]: ∃ P : Sylow p G, H ≤ P := by
  have h1 : ∃ P : Sylow p G, card (orbit H P) = 1 := by sorry -- Sylow II
  cases' h1 with P h1
  have h2 : P ∈ orbit H P := by apply mem_orbit_self
  --rw [card_eq_one_iff] at h1
  have h3 : orbit H P = {P} := card_stuff (orbit H P) P h2 h1
  have hn : H ≤ Subgroup.normalizer P := by
    rw[SetLike.le_def] --- die
    intros h h5
    --- have h : H := ⟨h, h5⟩
    rw [← normal]
    rw [orbit] at h3
    have h : H := by sorry
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
  --have : R : Sylow p G := by sorry
  have h4 : Q ≤ (R : Sylow p G).normalizer := by sorry --- same as Sylow III
  apply normaliser at h4
  have h5 : (R : Sylow p G).toSubgroup = Q := Q.3 (R : Sylow p G).2 h4
  simp [Ω] at R
  rcases R with ⟨R, ⟨g, hg⟩⟩
  use g
  rw [hg]
  simp only at h5
  exact Sylow.ext h5
  exact Q.2

-- theorem SylowIV [Finite (Sylow p G)](P : Sylow p G) : Sylow p G = {g • P | g : G} := by
--   sorry
