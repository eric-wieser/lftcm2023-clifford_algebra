import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Sign

noncomputable section

#check ExteriorAlgebra
variable (R) [CommRing R] (n : ℕ)
variable  (ι : Type) [LinearOrder ι]

-- a list of indices, sorted
abbrev Model.Index := {l : List ι // l.Sorted (· < ·) }

def Model := Model.Index ι →₀ R

instance : AddCommGroup (Model R ι) := by
  unfold Model
  infer_instance
instance : Module R (Model R ι) := by
  unfold Model
  infer_instance

variable {R ι} in
def Model.ofFinsupp : ( Model.Index ι →₀ R) ≃ₗ[R] Model R ι :=
  LinearEquiv.refl _ _

instance : One (Model R ι) where
  one := Model.ofFinsupp <| Finsupp.single ⟨[], by simp⟩ 1

  /-
  # todos
  define multiplication, prove associativity

  instance : Ring (Model R ι)
  instance : Algebra R (Model R ι)

  square single should give quadratic form
  -/

variable { ι }
def Model.single ( i : ι ) : Model R ι :=
  Model.ofFinsupp <| Finsupp.single {
    val := [i]
    property := by
      simp
  } 1

set_option pp.proofs.withType false

#check Model.single ℤ (1 : Fin 3) + (3:ℤ) • Model.single ℤ (2 : Fin 3)


def mul_helper : Model.Index ι → Model.Index ι → Model.Index ι × SignType :=
  sorry

lemma single_mul_single_helper (i : ι) :
  (mul_helper ⟨[i], by simp⟩ ⟨[i], by simp⟩).2 = 0 := by
  sorry

-- def list_sort_concat
open scoped BigOperators

variable {R}
def mul (v w : Model R ι) : Model R ι :=
  (Model.ofFinsupp.symm v).sum fun i vi ↦
    (Model.ofFinsupp.symm w).sum fun j wj ↦
      let ⟨k,s⟩:=mul_helper i j
      Model.ofFinsupp <| Finsupp.single k (s * vi * wj)

instance : Mul (Model R ι) where
  -- multiply pairwise
  mul v w :=
  (Model.ofFinsupp.symm v).sum fun i vi ↦
    (Model.ofFinsupp.symm w).sum fun j wj ↦
      let ⟨k,s⟩:=mul_helper i j
      Model.ofFinsupp <| Finsupp.single k (s * vi * wj)

#print instMulModel

lemma single_mul_single (i : ι) : Model.single R i * Model.single R i = 0 := by
  change Finsupp.sum _ _ = _
  dsimp only [mul,Model.single]
  simp
  sorry

#check Finsupp.sum_single_index


instance : Ring (Model R ι) where
  -- inheritance in lean 4 is (somewhat) broken currently
  __ := inferInstanceAs (AddCommGroup (Model R ι))

  left_distrib := sorry
  right_distrib := sorry

  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : Algebra R (Model R ι) where
  toFun := Finsupp.single ⟨[], by simp⟩
  map_one' := rfl
  map_mul' := sorry
  -- we came up with this by using `by simp`
  map_zero' := Finsupp.single_zero _
  map_add' x y := sorry
  commutes' r x := sorry
  smul_def' r x := sorry

variable {R}
variable {A : Type} [Ring A] [Algebra R A]
variable {M : Type} [AddCommGroup M] [Module R M]

def liftToFun ( f : (ι →₀ R) →ₗ[R] A ) ( hf : ∀ m, f m * f m = 0 ) : (Model R ι →ₐ[R] A) where
  toFun m := m.sum $ λ ⟨i, _⟩ r => (List.prod (List.map f (i.map (λ _ => 0))))
  -- toFun m := m.sum fun ⟨i, _⟩ r => r • (List.prod (List.map f (List.map (λ _ => 0) i)))

  -- toFun m := m.sum
  --   λ ⟨basis_elem, _⟩ scaler =>
  --     (List.prod
  --       (List.map f (List.map (λ _ => _) basis_elem)))

      -- ((List.map f (List.map (λ v => {
      --   support := v
      --   toFun := λ _ => scaler
      --   mem_support_toFun := by
      --     simp
      --     intro h
      --     constructor
      --     . sorry
      --     . sorry
      -- }) basis_elem)).prod)
  -- toFun m := m.sum fun ⟨basis_elem, _⟩ r => (List.prod (List.map f _))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry


def liftInvFun : (Model R ι →ₐ[R] A) → { f : (ι →₀ R) →ₗ[R] A // ∀ m, f m * f m = 0 } := sorry

-- @[simps! symm_apply]
def lift :
    { f : (ι →₀ R) →ₗ[R] A // ∀ m, f m * f m = 0 }
    ≃ (Model R ι →ₐ[R] A)
    where
      toFun := liftToFun
      invFun := liftInvFun
      left_inv := sorry
      right_inv := sorry

