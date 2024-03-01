import Mathlib.Tactic

set_option autoImplicit false --stops me accidentally rewriting my variables
variable (G H : Type) {X : Type} [Group G] [MulAction G X] (x y z : X)
variable(H : Subgroup G)
variable {a b : G}


open MulAction

/- ### Orbit Stabiliser Theorem ###-/


/- # Defining our maps -/


/--The map from the quotient group of the stabilizer to the set X, for an element x-/
-- aka φ, before the restriction to its image
def ψ (g : G ⧸ stabilizer G x) : X :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (QuotientGroup.leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]


--showing that its image is the orbit
lemma ψ_orbit (g) : ψ G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩


/--The restricted map from the quotient of the stabilizer to the orbit of the element x-/
--supplying the output and a proof that this is in our range
def φ : G ⧸ stabilizer G x → (orbit G x) := fun g => ⟨ψ G x g, ψ_orbit G x g⟩


--a lemma so that we can rewrite our range elements φ G x, directly as the group action g • x
lemma φ_mk' (g : G) : φ G x (QuotientGroup.mk g) = ⟨g • x, mem_orbit x g⟩ := rfl

set_option pp.proofs.withType false --so I can read


/- # Proving bijectivity -/


--lemma following directly from the real life proof, a(x) = b(x) => a⁻¹b ∈ Stab(x)
lemma eq_imp_stab :(φ G x a = φ G x b) → (a⁻¹*b ∈ stabilizer G x):= by
  intro p
  repeat rw [φ_mk'] at p
  apply Subtype.val_inj.2 at p
  dsimp at p
  have  h: (a⁻¹ * b) • x = a⁻¹ • (b • x) := by rw [mul_smul a⁻¹ b x]
  rw [← p, smul_smul a⁻¹ a x, inv_mul_self, one_smul] at h
  exact h

/--Proof of the injectivity of φ-/
theorem injective_φ : Function.Injective (φ G x) :=  by
  simp [Function.Injective]
  intros p q h
  obtain ⟨a, ha⟩ := Quot.exists_rep p
  obtain ⟨b, hb⟩ := Quot.exists_rep q
  have ha: ↑a = p := by exact ha
  have hb: ↑b = q := by exact hb
  have h2: φ G x ↑a = φ G x ↑b := by
    rw [←ha, ←hb] at h
    exact h
  apply eq_imp_stab at h2
  rw [←QuotientGroup.eq'] at h2
  rw [←ha, ←hb]
  exact h2


--like before, so we can rewrite an orbit element directly
lemma orbit_def : y ∈ orbit G x → ∃ g : G, y = g • x := by
  simp[orbit]
  intros a h
  use a
  simp [h]


/--Proof of the surjectivity of φ-/
theorem surjective_φ: Function.Surjective (φ G x) := by
  simp[Function.Surjective]
  intros y h1
  have h2 : y ∈ orbit G x → ∃ g : G, y = g • x := by apply orbit_def
  apply h2 at h1
  cases' h1 with a h3
  use a
  ext
  simp
  rw [h3, φ_mk']


/--Orbit Stabliser Theorem : proof of the bijectivity of φ-/
theorem orbit_stab_bij : Function.Bijective (φ G x) := by
  simp[Function.Bijective, injective_φ, surjective_φ]


/--Orbit Stabiliser Theorem : the equivalence between the quotient of the stabiliser and the orbits -/
noncomputable def orbit_stab_equiv : (G ⧸ stabilizer G x ≃ orbit G x) :=  by
  apply Equiv.ofBijective
  simp [Function.Bijective]
  constructor
  apply injective_φ
  apply surjective_φ


/- # Cardinality equivalence -/

/--| X ⧸ G | : The set of orbits of X -/
local notation "Φ" => Quotient <| orbitRel G X


/- # Note #
From now on we are working with finite G and X, in order to use proofs about the cardinalities
-/

--some more variables we need, and casting all our groups/sets to Fintypes
variable (N : Subgroup G) [Subgroup.Normal N] (X)
variable (α β : Type) [Fintype α] [Fintype β] --only needed for bijection_imp_eq_card
variable[Fintype G] [Fintype X] [MulAction G X] [Fintype Φ]
variable[Fintype (G ⧸ stabilizer G x)] [∀ x : X, Fintype <| stabilizer G x] [∀ x : X, Fintype (orbit G x)] [∀ g : G, Fintype <| fixedBy X g]
variable {G} (g)

--a lemma because lean doesn't like when you divide with natural numbers
--ideally, I would rewrite this proof without the use of / altogether
lemma cant_use_ℕ  (w v : ℕ) : (w *  v / v = w) := by sorry


/--Proof that | G ⧸ N | = | G | / | N | . Follows from Lagrange's Theorem-/
theorem quotient_order [Fintype G] [Fintype N] [Fintype (G ⧸ N)][DecidablePred fun a => a ∈ N]: Fintype.card G / Fintype.card N = Fintype.card (G ⧸ N) := by
  simp [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  simp [cant_use_ℕ]
  -- I have no idea why rfl does not work here :(
  sorry

--a proof that if we have a bijection then the cardinalities of the (finite) domain and range are equal
lemma bijection_imp_eq_card (f : α → β) (hf : Function.Bijective f) [Fintype (Set.range f)]: Fintype.card α = Fintype.card β := by
  rw [Function.Bijective] at hf
  cases' hf with hInj hSur
  have h_f_imag_eq_β : Set.range f = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro B
    exact hSur B
  have h_f_imag_card : Fintype.card (Set.range f) = Fintype.card α := Set.card_range_of_injective sorry
  rw [← h_f_imag_card]
  exact (set_fintype_card_eq_univ_iff (Set.range f)).mpr h_f_imag_eq_β


/-- Finite version of φ, our orbit stabiliser bijection-/
--casting our function φ so that Fintype likes it
--I don't know why this has to be a def, but the linting said so
noncomputable def fin_φ [Fintype G] : Fintype (Set.range (φ G x)) := by exact Fintype.ofFinite (Set.range (φ G x))



/--Orbit Stabiliser Theorem : a proof that | G | ⧸ | Stab(x) | = | G(x) | -/
theorem orbit_eq_card : Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (orbit G x) := by
  have h1 : Function.Bijective (φ G x) := by apply orbit_stab_bij
  have h2 : DecidablePred fun a => (a ∈ stabilizer G x) :=  by exact g
  have h3: Fintype.card (G) / Fintype.card (stabilizer G x) = Fintype.card (G ⧸ stabilizer G x) := by apply quotient_order (stabilizer G x)
  rw [h3]
  let _ : Fintype (Set.range (φ G x)) := fin_φ _ _
  apply bijection_imp_eq_card (G ⧸ stabilizer G x) (orbit G x) (φ G x) h1



open BigOperators -- to use ∑

/-### Burnsides Lemma ###-/


--these are some lemmas which rearrange the orbit stabiliser theorem into Burnsides Lemma
--rearranging equations with natural numbers is very difficult
lemma fix_stab_equiv : ∑ g : G, Fintype.card (fixedBy X g) = ∑ x : X, Fintype.card (stabilizer G x) := by sorry


lemma sum_orbits [Fintype Φ] :(Fintype.card Φ) = ∑ x : X, 1 / (Fintype.card (orbit G x)) := by sorry


--this one follows pretty directly from the orbit stabiliser theorem
lemma orbit_stab [∀ x : X, Fintype <| stabilizer G x]
: ∑ x : X, 1 / Fintype.card (orbit G x) =  1 / (Fintype.card (G) /(∑ x : X ,Fintype.card (stabilizer G x))):= by sorry


--again, a lemma because I am dividing natural numbers, I should avoid using it or cast the cardinalities as reals/rationals
lemma cant_div_ℕ  (w v: ℕ ) : 1 / (w / v) = v / w := by sorry


/--Burnside's Lemma : a corollary of the Orbit Stabliser Theorem-/
theorem burnside_lemma [Fintype Φ] : (Fintype.card Φ) =  (∑ g : G, Fintype.card (fixedBy X g)) / Fintype.card G := by
 rw [sum_orbits, orbit_stab]
 simp [fix_stab_equiv, cant_div_ℕ]



/- Introduces inductive type MyD₃ and its constructors. It is to become the Dihedral Group of the 3-gon (Triangle)
with the r i corresponding to rotations by 0, 120 and 240 degrees and the sr i corresponding to its
3 reflective symmetries -/
inductive MyD₃
  | r : ZMod 3 → MyD₃
  | sr: ZMod 3 → MyD₃
deriving Fintype

namespace MyD₃

/- Defines the multiplication (Group Law) of elements of D₃. The indices i and j take values
of 0,1 and 2-/
def mul : MyD₃ → MyD₃ → MyD₃
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/- Defines the multiplicative identity of MyD₃ as r 0-/
def one : MyD₃ := r 0

/- Map which generates the multiplicative inverse of any element of MyD₃ -/
def inv : MyD₃ → MyD₃
  | r i => r (-i)
  | sr i => sr i

/- Proof that the multiplication defined is associative -/
lemma D₃_assoc (a b c : MyD₃) : mul (mul a  b)  c =  mul a  (mul b  c) := by
  cases' a with a1 a2
  · cases' b with b1 b2
    · cases' c with c1 c2
      · simp [mul]
        ring
      · simp [mul]
        ring
    · cases' c with c1 c2
      · simp [mul]
        ring
      · simp [mul]
        ring
  · cases' b with b1 b2
    · cases' c with c1 c2
      · simp [mul]
        ring
      · simp [mul]
        ring
    · cases' c with c1 c2
      · simp [mul]
        ring
      · simp [mul]
        ring

/- Left multiplication by the identity leaves any element unchanged -/
lemma D₃_one_mul (g : MyD₃): mul one g = g := by
  cases' g with g1 g2
  · simp [one, mul]
  · simp [one, mul]

/- Right multiplication by the identity leaves any element unchanged -/
lemma D₃_mul_one (g : MyD₃): mul g one  = g := by
  cases' g with g1 g2
  · simp [one, mul]
  · simp [one, mul]

/- Multiplication by the inverse returns the identity function -/
lemma D₃_mul_left_inv (g : MyD₃) : mul (inv g) g = one := by
  cases' g with g1 g2
  · simp [inv, mul, one]
  · simp [inv, mul, one]

/- Verification that MyD₃ and the multiplication defined satisfy the criteria to be a group-/
instance : Group MyD₃ where
  mul := mul
  mul_assoc := by exact D₃_assoc
  one := one
  one_mul := by exact D₃_one_mul
  mul_one := by exact D₃_mul_one
  inv := inv
  mul_left_inv := by exact D₃_mul_left_inv

/- The order of MyD₃ is 6 -/
lemma My_D₃_card : Fintype.card MyD₃ = 6 := by rfl

end MyD₃

variable (n : ℕ)

/- Constructs a set of natural numbers containing n distinct elements: 0 to n-1 -/
def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)

/- Constructs a  new type, objects of this type are ordered lists of length 7, their entries taken from set (n_set n) -/
def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

/- Demonstration of a different approach which avoids some difficulties caused by (n7 n) being a type not a set -/
#check Set.pi (@Finset.univ (Fin 7) _).toSet (fun _ => n_set n)

/- Visual example of an object of type (n7 n) -/
def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

/- Functions which permute the entries of an element of (n7 n). The elements of (n7 n) have been designed as abstractions of a problem involving
colourings of a triangular pattern, these functions correspond to rotations and refelections of these colourings -/
def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

open MyD₃

/- Defines the group action of elements of MyD₃ on 'set' (n7 n) -/
def transform_action : MyD₃ → n7 n → n7 n
| r 0 => id
| r 1 => rotation_funct n
| r 2 => (rotation_funct n) ∘ (rotation_funct n)
| sr 0 => reflection_0_funct n
| sr 1 => reflection_1_funct n
| sr 2 => reflection_2_funct n

/- r 0 acts on elements of (n7 n) by leaving them unchanged -/
lemma identity_action (x : n7 n) : (transform_action n) (r 0) x = x := by exact rfl

/- Associativity of the group action. Left sorried as would be repetitive proof considering cases, as seen previously -/
lemma assoc_action (g₁ g₂ : MyD₃)(x : n7 n) :
  (transform_action n) (g₁ * g₂) x = (transform_action n g₁) (transform_action n g₂ x) := by
  sorry

/- Verification that transform_action satisfies the criteria to be a valid group action of MyD₃ on (n7 n) -/
instance : MulAction MyD₃ (n7 n) where
  smul := transform_action n
  one_smul := identity_action n
  mul_smul := assoc_action n

/- g • x is equal to transform_action applied to an element of D₃ and  (n7 n) -/
theorem trans_action_def (g : MyD₃)(x : n7 n) : g • x = transform_action n g x := by rfl

/- Defining shorter notation for convenience -/
local notation "Ψ" => Quotient <| orbitRel MyD₃ (n7 n)

/- Casting variables as Fintypes as project focused on finite groups and finite sets -/
variable (x : n7 n)
variable [Fintype (MyD₃ ⧸ stabilizer MyD₃ x)][∀ x : (n7 n), Fintype <| stabilizer MyD₃ x][∀ x : (n7 n), Fintype (orbit MyD₃ x)][∀ g : MyD₃ , Fintype <| fixedBy (n7 n) g]
variable [Fintype Ψ][Fintype (n7 n)]

/- The set of points of (n7 n) fixed under group action by r 0 is the entirety of (n7 n) -/
lemma r0_fixed : MulAction.fixedBy (n7 n) (r 0) = Set.univ := by
  simp [MulAction.fixedBy]
  have r0_id (y : n7 n) : r 0 • y = y := by rfl
  simp_all

/-The cardinality of set fix(r 0) is n⁷. An issue arises due to (n7 n) being a type not a set so cardinality is not defined -/
lemma r0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 0)) = n^7 := by
  rw [r0_fixed]
  rw [Set.univ]
  sorry

/- Demonstration that an ordered list in (n7 n) with form (a, a, a, b, b, b, c) is fixed under group action by r 1-/
lemma r1_fix_demonstration (a1 b1 c1 : n_set n) : ((a1, a1, a1, b1, b1, b1, c1) : n7 n) ∈ MulAction.fixedBy (n7 n) (r 1) := by
  simp [MulAction.fixedBy]
  constructor

/- The set of ordered lists with form (a, a, a, b, b, b, c) is the fix(r 1)-/
lemma r1_fixed : MulAction.fixedBy (n7 n) (r 1) =
{(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}:= by
  have form_imp_fix (x : n7 n) :
  x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} → x ∈ MulAction.fixedBy (n7 n) (r 1) := by
    intro hx
    refine MulAction.mem_fixedBy.mpr ?_
    sorry
  have nform_imp_nfix (x : n7 n) :
  ¬ (x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}) → ¬(x ∈ MulAction.fixedBy (n7 n) (r 1)) := by
    sorry
  have form_iff_fix (x : n7 n) :
  x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} ↔ x ∈ MulAction.fixedBy (n7 n) (r 1) := by
    constructor
    exact form_imp_fix x
    contrapose
    exact nform_imp_nfix x
  sorry

/- The cardinality of fix(r 1) is n³ -/
lemma r1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 1)) = n^3 := by
  rw [r1_fixed]
  sorry

/- Repeated process of obtaining the cardinalities of fix(g) for all g in MyD₃ for application of Burnside's Lemma -/

-- lemma r2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 2)) = n^3 := by
-- sorry

-- lemma sr0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

-- lemma sr1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 1)) = n^5 := by
-- sorry

-- lemma sr2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

/- The finite sum of the cardinalities of fix(g) as g varies across MyD₃ is n⁷ + 3n⁵ + 2*n^3 -/
lemma action_fix_sum  : ∑ g : MyD₃,  Fintype.card (MulAction.fixedBy (n7 n) g) = n^7 + 3*n^5 + 2*n^3 := by
  sorry

/- The cardinality of the set of orbits of MyD₃ acting on (n7 n) is proven via the Burnside Lemma to be
(n⁷ + 3n⁵ + 2*n^3)/6. In the context of the colouring puzzle, this corresponds to the number of unique colourings
of the triangle's 7 sections when there are n colours available. -/
theorem colouring_card [Fintype Ψ] : Fintype.card (Ψ) = (n^7 + 3*n^5 + 2*n^3)/6:= by
  rw [burnside_lemma]
  rw [action_fix_sum]
  rw [My_D₃_card]
