import Mathlib.Tactic

inductive MyD₃
  | r : ZMod 3 → MyD₃
  | sr: ZMod 3 → MyD₃
deriving DecidableEq, Fintype

namespace MyD₃

def D₃GroupLaw : MyD₃ → MyD₃ → MyD₃
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

def D₃id : MyD₃ := r 0

def D₃inv : MyD₃ → MyD₃
  | r i => r (-i)
  | sr i => sr i

instance : Group MyD₃ where
  mul := D₃GroupLaw
  mul_assoc := by sorry
  one := D₃id
  one_mul := by sorry
  mul_one := by sorry
  inv := D₃inv
  mul_left_inv := by sorry

/- instance : Fintype MyD₃ where
  elems := {r 0, r 1, r 2, sr 0, sr 1, sr 2}
  complete := by
    intro x
    cases' x with a1 a2
    fin_cases a1
    simp
    simp
    simp
    right
    right
    rfl
    fin_cases a2
    simp
    simp
    aesop -/

/-Fintype.ofEquiv-/


lemma MyD₃_card : Fintype.card MyD₃ = 6 := by rfl

/- Prove any theorems about the definitions of multiplication, idetities and inverses and so on here.
such as
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) := rfl
 Also results about cardinality perhaps

 theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
#align dihedral_group.card DihedralGroup.card

theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]
   -/

end MyD₃

variable (n : ℕ)

def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)
#check Set.pi (@Finset.univ (Fin 7) _).toSet (fun _ => n_set n)
def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

open MyD₃

def transform_action : MyD₃ → (n7 n → n7 n)
| r 0 => id
| r 1 => rotation_funct n
| r 2 => (rotation_funct n) ∘ (rotation_funct n)
| sr 0 => reflection_0_funct n
| sr 1 => reflection_1_funct n
| sr 2 => reflection_2_funct n

lemma identity_action (x : n7 n) : (transform_action n) (r 0) x = x := by exact rfl

lemma assoc_action (g₁ g₂ : MyD₃)(x : n7 n) :
(transform_action n) (g₁ * g₂) x = (transform_action n g₁) (transform_action n g₂ x) := by
sorry

instance : MulAction MyD₃ (n7 n) where
  smul := transform_action n
  one_smul := identity_action n
  mul_smul := assoc_action n

theorem trans_action_def (g : MyD₃)(x : n7 n): g • x = transform_action n g x := by rfl

lemma r0_fixed : MulAction.fixedBy (n7 n) (r 0) = Set.univ := by
simp [MulAction.fixedBy]
have r0_id (y : n7 n) : r 0 • y = y := by rfl
simp_all

lemma r1_fixed : MulAction.fixedBy (n7 n) (r 1) =
{(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}:= by
simp [MulAction.fixedBy]
simp [trans_action_def]
sorry
