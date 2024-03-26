import Mathlib

/-# Sylow Theorems yay-/

/- # Preliminaries -/
variable (p : ℕ) (G H : Type*) [Group G] {H J: Subgroup G} {pCond : Fact p.Prime}
variable {p} {G}

open BigOperators MulAction Fintype


def φ (H J : Subgroup G) : (H × J) → G := fun g => g.1 * g.2

---example [Fintype P] [Fintype Q] [Fintype (P ⊓ Q).toSubgroup] (P Q : Subgroup G): Finset.inf (P ⊓ Q) id := by sorry
lemma PQmul (P : Sylow p G) (Q : Subgroup G) (norm: Q ≤ P.normalizer): ∀ {a b : G}, a ∈ Set.range (φ Q ↑P) → b ∈ Set.range (φ Q ↑P) → a * b ∈ Set.range (φ Q ↑P) := by
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

lemma PQinv (P : Sylow p G) (Q : Subgroup G) (norm: Q ≤ P.normalizer): ∀ {x : G}, ∀ x_1 ∈ Q, ∀ x_2 ∈ P.1, x_1 * x_2 = x → ∃ a ∈ Q, ∃ a_1 ∈ P.1, a * a_1 = x⁻¹ := by
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

lemma normaliser (P : Sylow p G) (Q : Subgroup G) (h : IsPGroup p Q): Q ≤ P.normalizer → Q ≤ P := by
  intro norm
  let PQ : Subgroup G := {
    carrier := Set.range (φ Q P)
    mul_mem' := PQmul P Q norm
    one_mem' := ⟨1, by simp [φ]⟩
    inv_mem' := by
      simp [φ]
      exact PQinv P Q norm
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

theorem SylowI (a m : ℕ) [Fintype G] [Fintype H] (h :¬ (p ∣ m)): Fintype.card G = p ^ a * m  → Fintype.card H = p^a:= sorry --exists_subgroup_card_pow_prime

/- # Sylow II
Number of Sylow p-groups
nₚ(G) ≡ 1 % p -/



lemma orbit_div_G [Fintype G] (y : X) [Fintype <| orbit G y] [Fintype <| stabilizer G y] : Fintype.card (orbit G y) ∣ Fintype.card G  := by
  simp [Nat.instDvdNat]
  have orb_stab := card_orbit_mul_card_stabilizer_eq_card_group G y --Orbit-stabliser theorem
  exact ⟨card ↥(stabilizer G y), orb_stab.symm⟩


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


--def something {ψ : Ω → (Sylow p G)} (hφ : Function.LeftInverse Quotient.mk'' ψ) : (Sylow p G) ≃ Σω : Ω, G ⧸ stabilizer G (ψ ω) := sorry

theorem SylowII [Fintype (Sylow p G)](P : Sylow p G)[Fintype P](Q : Sylow p G)[∀ x : Sylow p G, Fintype (orbit P x)][Fintype <| stabilizer P Q][Fintype (Quotient <| orbitRel P (Sylow p G))]:
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
    intro h9
    have h9' := h9
    rw [← mem_fixedPoints_iff_card_orbit_eq_one, h] at h9'
    simp at h9'
    have : Q ∈ orbit P Q := mem_orbit_self Q
    nth_rw 1 [h9'] at this
    exact card_stuff (orbit P Q) P this h9
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
  have ψ : Quotient (orbitRel P (Sylow p G)) → Sylow p G := by sorry -- fun y => element of orbit
  have : card (Sylow p G) = ∑ y : Quotient (orbitRel P (Sylow p G)), card (orbit P (ψ y)) := by sorry --orbit stab

--- convert unique orbit order one + other orbits div by p to final form
  sorry


/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/


-- variable [Fintype (Sylow p G)][∀ q : Sylow p G, Fintype (orbit H q)]

lemma orbit_def : y ∈ orbit G x ↔ ∃ g : G, y = g • x := by
  constructor
  simp[orbit]
  intros a h
  use a
  simp [h]
  simp[orbit]
  intros a b
  use a
  exact id b.symm

lemma orbit_def' (g : G) : g • x ∈ orbit G x := by exact mem_orbit x g



theorem SylowIII (h : IsPGroup p H)[∀ q : Sylow p G, Fintype (orbit H q)]: ∃ P : Sylow p G, H ≤ P := by
  have h1 : ∃ P : Sylow p G, card (orbit H P) = 1 := by sorry -- Sylow II
  cases' h1 with P h1
  have h2 : P ∈ orbit H P := by apply mem_orbit_self
  --rw [card_eq_one_iff] at h1
  have h3 : orbit H P = {P} := card_stuff (orbit H P) P h2 h1
  have hn : H ≤ Subgroup.normalizer P := by
    rw[SetLike.le_def] --- die
    intros h h5
    ---have h : H := ⟨h, h5⟩
    rw [← normal]
    have hm  := mem_orbit P (⟨h, h5⟩ : H)   --- ⟨⟨h, h5⟩, by simp[orbit]; sorry⟩ mem_orbit P h
    rw [h3] at hm
    simp at hm
    exact hm
  use P
  apply normaliser
  exact h
  exact hn

/- # Sylow IV
Sylₚ(G) is a single conjugacy class

∀ Q, P ∈ Sylₚ(G), ∃ g s.t Q = ᵍP -/
-- variable (P : Sylow p G)
-- local notation "Ω" => {g • P | g : G}

lemma hom (G : Type*) [Group G] (S T : Type*) [MulAction G S] [MulAction G T]
   (φ : MulActionHom G S T) (s : S) : φ '' (orbit G s) = orbit G (φ s) := by
 ext x
 constructor
 · rintro ⟨-, ⟨g, rfl⟩, rfl⟩
   simp
 · rintro ⟨g, rfl⟩
   use g • s
   simp

example [Finite X](X : Set S) (Y := {a | a ∈ X}) : Set.Finite Y := by sorry

--example(a g c : G) : ∃ g,  g • P = c • P := by exact exists_apply_eq_apply (fun a_1 => a_1 * a) c

theorem SylowIV [Finite G] [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) := by
  constructor
  intros P Q

  let Ω := {g • P | g : G}
  let φ : MulAction Q Ω := {
    smul := fun q y => ⟨q • y, by
      simp only [Ω] at *
      rcases y with ⟨a, b, rfl⟩
      use q * b
      --simp only
      exact mul_smul (q : G) b P⟩
    one_smul := by
      intro b
      simp only [Ω] at *
      rcases b with ⟨a, c, rfl⟩
      --congr!
      sorry
      --apply exists_apply_eq_apply (fun a_1 => a_1 • P) c
      -- rw [←mul_smul 1 c P, one_mul]

    mul_smul := by
      intros x y b
      simp only [Ω] at *

      sorry
  }
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (Sylow p G)
  have _ : ∀ x : Ω, Fintype (orbit Q x) := by sorry
  have _ : Finset Ω := by sorry
  let I := Fintype.ofFinite Ω
  have h1 : card Ω ≡ 1 [MOD p] := by sorry --Sylow II
  have h2 : ∃ R : Ω, card (orbit Q R) = 1 := by sorry
  rcases h2 with ⟨R, hR⟩
  have h3 : orbit Q R = {R} := card_stuff (orbit Q R) R (mem_orbit_self R) hR
  let f : MulActionHom Q Ω (Sylow p G) := {
    toFun := fun x => x
    map_smul' := by intros ; rfl
  }
  have h4 : Q ≤ (R : Sylow p G).normalizer := by
    rw[SetLike.le_def] --- die
    intros h h5
    have h210 : orbit Q (R : Sylow p G) = {(R : Sylow p G)} := by
      change orbit Q (f R) = {f R}
      rw [← hom]
      simp [f]
      aesop
    ---have h : H := ⟨h, h5⟩
    rw [← normal]
    --rw [h3] at h210
    have hm  := mem_orbit (R : Sylow p G) (⟨h, h5⟩ : ↑Q)   --- ⟨⟨h, h5⟩, by simp[orbit]; sorry⟩ mem_orbit P h
    --rw [hm] at h210
    rw [h210] at hm
    simp at hm
    exact hm

   --- same as Sylow III
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
