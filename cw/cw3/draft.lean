import Mathlib

variable (p : ℕ) (G H : Type*) [Group G] {H J: Subgroup G} {pCond : Fact p.Prime}
variable {p} {G}

open BigOperators MulAction Fintype

/-# The Sylow Theorems
Formalising Mathematics CW3 -/

/- # Preliminaries
I start by proving the Proposition 2.1 and Lemma 2.2 as in Liebeck's proof.
To prove PQ is a subgroup I first define a map from (P × Q) → PQ and then proof the subgroup axioms
The cardinality parts of Prop 2.1 and therefore Lemma 2.2 are missing.
We only need that PQ is a p-subgroup (which follows) and then we are done. -/

/-- φ : (P × Q) → PQ -/
def φ (H J : Subgroup G) : (H × J) → G := fun g => g.1 * g.2

lemma PQmul (P : Sylow p G) (Q : Subgroup G) (norm: Q ≤ P.normalizer): ∀ {a b : G}, a ∈ Set.range (φ Q ↑P) → b ∈ Set.range (φ Q ↑P) → a * b ∈ Set.range (φ Q ↑P) := by
  simp [φ]
  intros _ _ q1 hq1 p1 hp1 a q2 hq2 p2 hp2 b
  have h0 : q2⁻¹ ∈ P.normalizer := by
    rw [SetLike.le_def] at norm
    exact Subgroup.inv_mem (Subgroup.normalizer P) (norm hq2)
  have h1 : (q2⁻¹ * p1 * q2) * p2 ∈ P := by
    apply mul_mem
    · rw [h0] at hp1
      simp at hp1
      exact hp1
    · exact hp2
  use q1 * q2
  constructor
  · exact Subgroup.mul_mem Q hq1 hq2
  · use (q2⁻¹ * p1 * q2) * p2
    constructor
    · exact h1
    · simp_rw [←a, ←b, mul_assoc]
      simp only [mul_inv_cancel_left]

lemma PQinv (P : Sylow p G) (Q : Subgroup G) (norm: Q ≤ P.normalizer): ∀ {x : G}, ∀ x_1 ∈ Q, ∀ x_2 ∈ P.1, x_1 * x_2 = x → ∃ a ∈ Q, ∃ a_1 ∈ P.1, a * a_1 = x⁻¹ := by
  intros a q hq p hp ha
  use q⁻¹
  constructor
  · exact inv_mem hq
  · use q * p⁻¹ * q⁻¹
    constructor
    · have : q ∈ P.normalizer := by
        rw [SetLike.le_def] at norm
        exact norm hq
      --simp only [Subgroup.normalizer] at this
      /- I've left some of the unecessary simps in as comments, in case it helps when marking-/
      apply inv_mem at hp
      rw [this] at hp
      exact hp
    · simp_rw [← ha, mul_assoc]
      simp only [inv_mul_cancel_left, mul_inv_rev]

/--Q ≤ N(P) → Q ≤ P, where P ∈ Sylₚ(G) and Q is a p-subgroup
A combination of Proposition 2.1 and Lemma 2.2-/
lemma norm_imp_sub (P : Sylow p G) (Q : Subgroup G) (h : IsPGroup p Q): Q ≤ P.normalizer → Q ≤ P := by
  intro norm
  let PQ : Subgroup G := {
    carrier := Set.range (φ Q P)
    mul_mem' := PQmul P Q norm
    one_mem' := ⟨1, by simp [φ]⟩
    inv_mem' := by
      simp [φ]
      exact PQinv P Q norm}
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
    · apply one_mem
    · use a
      constructor
      · exact ha
      · apply one_mul
  have : PQ = P := by
    rcases P with ⟨a, b, c⟩
    exact c h5 h6
  have h7 : Q ≤ PQ := by
    rw [SetLike.le_def]
    intros a ha
    simp [φ]
    use a
    constructor
    · exact ha
    · use 1
      constructor
      · apply one_mem
      · apply mul_one
  rw [←this]
  exact h7

lemma norm_def {g : G} {P : Sylow p G} : g ∈ (P : Subgroup G).normalizer ↔ g • P = P  := Sylow.smul_eq_iff_mem_normalizer.symm

/- # Sylow I
Existence of Sylow p-groups
|G| = pᵃm (p ∤ m) → G has a subgroup of order pᵃ -/

theorem SylowI {a m : ℕ} [Fintype G] (h :¬ (p ∣ m)): card G = p ^ a * m  → ∃ P : Subgroup G , [Fintype P] → Fintype.card P = p ^ a := by sorry
  -- follows from Sylow.exists_subgroup_card_pow_prime


/- # Sylow II
Number of Sylow p-groups
nₚ(G) ≡ 1 % p -/

/-- A corollary of the Orbit-Stabiliser Theorem
∣ orbit G x ∣ | ∣ G ∣ -/
lemma orbit_div_G [Fintype G] (y : X)[MulAction G X] [Fintype <| orbit G y] [Fintype <| stabilizer G y] : Fintype.card (orbit G y) ∣ Fintype.card G  := by
  simp [Nat.instDvdNat]
  have orb_stab := card_orbit_mul_card_stabilizer_eq_card_group G y --Orbit-stabliser theorem
  exact ⟨card ↥(stabilizer G y), orb_stab.symm⟩

--trivial in real life
lemma number_theory (a p n : ℕ ) (h1: a ∣ p ^ n) (h2 : a ≠ 1) (h3 : Fact p.Prime) : (p ∣ a) := by
  simp [fact_iff] at h3
  rcases n
  · simp only [Nat.zero_eq, pow_zero, Nat.dvd_one] at h1
    by_contra
    exact h2 h1
  · rw [Nat.dvd_prime_pow] at h1
    rcases h1 with ⟨k, ⟨_, hk'⟩⟩
    · rw [hk', Nat.dvd_prime_pow]
      · use 1
        have : k ≠ 0 := by
          intro hk1
          rw [hk1] at hk'
          exact h2 hk'
        constructor
        · exact Nat.one_le_iff_ne_zero.mpr this
        · simp only [pow_one]
      · exact h3
    · exact h3


-- also trivial in real life
lemma card_stuff (X : Set S)(x : S)[Fintype X] (h : x ∈ X) (h1: card X = 1) : X = {x} := by
  ext a
  constructor
  · intro h2
    simp only [Set.mem_singleton_iff]
    rw [card_eq_one_iff] at h1
    rcases h1 with ⟨⟨b, hb⟩ , hbp⟩
    have := hbp ⟨a, h2⟩
    simp only [Subtype.mk.injEq] at this
    rw [this]
    have := hbp ⟨x, h⟩
    simp only [Subtype.mk.injEq] at this
    rw [this]
  · intro h2
    --simp only [Set.mem_singleton_iff] at h2
    rw [h2]
    exact h

/-- Sylow's Second Theorem : nₚ(G) ≡ 1 % p -/
theorem SylowII [Fintype (Sylow p G)](P : Sylow p G)[Fintype P](Q : Sylow p G)[∀ x : Sylow p G, Fintype (orbit P x)][Fintype <| stabilizer P Q][Fintype (Quotient <| orbitRel P (Sylow p G))]:
  Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  -- We are considering the action of P on Sylₚ(G)
  -- ∃ an orbit of size one (P)
  have h1 : fixedPoints P (Sylow p G) = {P} := by
    apply Set.ext
    intro Q
    have h11 : Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q.normalizer := by
      rw [SetLike.le_def]
      simp only [mem_fixedPoints, Subtype.forall, Submonoid.mk_smul, norm_def]
    have h12 : Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by
      rw[h11]
      constructor
      · apply norm_imp_sub
        exact P.2
      · have : Q ≤ Q.normalizer := Subgroup.le_normalizer
        intros a _ c
        exact this (a c)
    have h13: P ≤ Q ↔ Q = P := by
      constructor
      · intro hpq
        rw [Sylow.ext_iff, P.3 Q.2 hpq]
      · exact fun a => Eq.le (id a.symm)
    rw [h12, h13]
    simp only [Set.mem_singleton_iff]
  have _ : Fintype (fixedPoints P (Sylow p G)) := by
    rw [h1]
    infer_instance
  have h2 : card (fixedPoints P (Sylow p G)) = 1 := by simp only [h1, card_ofSubsingleton]
  -- There are no other orbits of size one
  have h3 : card (orbit P Q) = 1 → (orbit P Q) = {P} := by
    intro h31
    have h32 := h31
    rw [← mem_fixedPoints_iff_card_orbit_eq_one, h1] at h32
    --simp only [Set.mem_singleton_iff] at h32
    have : Q ∈ orbit P Q := mem_orbit_self Q
    nth_rw 1 [h32] at this
    exact card_stuff (orbit P Q) P this h31
  -- All orbits must divide the order of P
  -- This is a corollary of the orbit-stabilizer theorem, rewritten as a lemma
  have h4 : card (orbit P Q) ∣  card P := orbit_div_G Q
  -- P = pⁿ
  have h5 [Fintype P] : ∃ n, card P = p ^ n := by
    obtain ⟨a, heq : card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
    use a
  rcases h5 with ⟨n, h5'⟩
  rw[h5'] at h4
  -- p divides all the orbits not equal to one
  have h6 : card (orbit P Q) ≠ 1 → p ∣ card (orbit P Q) := by
    intro nh2
    exact number_theory (card ↑(orbit P Q)) p n h4 nh2 pCond

  have ψ : Quotient (orbitRel P (Sylow p G)) → Sylow p G := by sorry -- fun y => element of orbit
  have : card (Sylow p G) = ∑ y : Quotient (orbitRel P (Sylow p G)), card (orbit P (ψ y)) := by sorry --orbit stab

--- convert unique orbit order one + other orbits div by p to final form
  sorry


/- # Sylow III
Every p-group is contained in a Sylow p-group
|Q| = p, Q ≤ G → ∃ P ∈ Sylₚ(G) s.t Q ≤ P
-/


/-- Sylow's Third Theorem : Every p-group is contained in a Sylow p-group-/
theorem SylowIII (h : IsPGroup p H)[∀ q : Sylow p G, Fintype (orbit H q)]: ∃ P : Sylow p G, H ≤ P := by
  have h1 : ∃ P : Sylow p G, card (orbit H P) = 1 := by sorry -- Sylow II
  --This result follows from norm_imp_sub
  rcases h1 with ⟨P, h1⟩
  have h2 : orbit H P = {P} := card_stuff (orbit H P) P (mem_orbit_self P) h1
  have h3 : H ≤ Subgroup.normalizer P := by
    rw[SetLike.le_def]
    intros h h5
    rw [norm_def]
    have h31  := mem_orbit P (⟨h, h5⟩ : H)
    rw [h2, Submonoid.mk_smul, Set.mem_singleton_iff] at h31
    exact h31
  use P
  exact norm_imp_sub P H h h3

/- # Sylow IV
Sylₚ(G) is a single conjugacy class

∀ Q, P ∈ Sylₚ(G), ∃ g s.t Q = ᵍP -/
-- variable (P : Sylow p G)
-- local notation "Ω" => {g • P | g : G}

-- Kevin wrote this :)
lemma hom (G : Type*) [Group G] (S T : Type*) [MulAction G S] [MulAction G T]
   (φ : MulActionHom G S T) (s : S) : φ '' (orbit G s) = orbit G (φ s) := by
 ext x
 constructor
 · rintro ⟨-, ⟨g, rfl⟩, rfl⟩
   simp
 · rintro ⟨g, rfl⟩
   use g • s
   simp

/-- Sylow's Fourth Theorem : Sylₚ(G) is a single conjugacy class-/
theorem SylowIV [Finite G] [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) := by
  constructor
  intros P Q
  let Ω := {g • P | g : G}
  -- Showing conjugation is well-defined from Ω → Ω
  let _ : MulAction Q Ω := {
    smul := fun q y => ⟨q • y, by
      rcases y with ⟨a, b, rfl⟩
      use q * b
      exact mul_smul (q : G) b P⟩
    one_smul :=  by
      intro b
      --simp only [Ω] at *
      rcases b with ⟨a, b, rfl⟩
      -- not sure why simp does nothing here
      -- congr! half fixes it
      -- this would be the last step if simp liked me:
      -- rw [←mul_smul 1 c P, one_mul]
      sorry
    mul_smul := by
      intros x y b
      --simp only [Ω] at *
      rcases b with ⟨a, b, rfl⟩
      -- same issue as before
      sorry
  }
  let _ := Fintype.ofFinite Ω
  have _ : ∀ x : Ω, Fintype (orbit Q x) := by sorry
  -- We have an orbit of size one, {R}
  have h1 : card Ω ≡ 1 [MOD p] := by sorry --Sylow II
  have h2 : ∃ R : Ω, card (orbit Q R) = 1 := by sorry --Sylow II
  rcases h2 with ⟨R, hR⟩
  have h3 : orbit Q R = {R} := card_stuff (orbit Q R) R (mem_orbit_self R) hR
  --This combined with the lemma hom allows us to rearrange the coercion ↑ and •
  --So that we can use norm_imp_sub
  let f : MulActionHom Q Ω (Sylow p G) := {
    toFun := fun x => x
    map_smul' := by intros ; rfl
  }
  -- Q ≤ N(R)
  have h4 : Q ≤ (R : Sylow p G).normalizer := by
    rw[SetLike.le_def]
    intros q hq
    have h41 : orbit Q (R : Sylow p G) = {(R : Sylow p G)} := by
      change orbit Q (f R) = {f R}
      rw [← hom]
      --simp only [Set.coe_setOf, Set.mem_setOf_eq]
      -- I found these using aesop :
      rename_i H_1 inst inst_1 inst_2 x x_1 x_2
      simp_all only [Set.coe_setOf, Set.mem_setOf_eq, card_ofSubsingleton, Set.image_singleton]
    rw [norm_def]
    have h42  := mem_orbit (R : Sylow p G) (⟨q, hq⟩ : ↑Q)
    rw [h41] at h42
    --simp only [Set.mem_setOf_eq, Submonoid.mk_smul, Set.mem_singleton_iff] at h42
    exact h42
  -- Q ≤ N(R) → Q = R (Q is maximal)
  apply norm_imp_sub at h4
  have h5 : (R : Sylow p G).toSubgroup = Q := Q.3 (R : Sylow p G).2 h4
  --simp only [Set.coe_setOf] at R
  -- Q ∈ Ω ∴ Ω = Sylₚ(G)
  rcases R with ⟨R, ⟨g, rfl⟩⟩
  · use g
    exact Sylow.ext h5
  · exact Q.2
