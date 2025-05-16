import Mathlib

open TensorAlgebra in
inductive MilnorK.Rel (K : Type*) [CommRing K] :
    TensorAlgebra ℤ (Additive Kˣ) →
    TensorAlgebra ℤ (Additive Kˣ) →
    Prop where
  | mk (a b : Kˣ) (h : (a : K) + b = 1) :
    MilnorK.Rel _ ((ι _ <| .ofMul a) * (ι _ <| .ofMul b)) 0

def MilnorK (K : Type*) [CommRing K] :=
  RingQuot <| MilnorK.Rel K

namespace MilnorK

variable {K : Type*} [CommRing K]

instance : Ring (MilnorK K) :=
  inferInstanceAs <| Ring <| RingQuot _

variable (K) in
def π : TensorAlgebra ℤ (Additive Kˣ) →+* MilnorK K :=
  RingQuot.mkRingHom _

variable (K) in
def ι : Additive Kˣ →+ MilnorK K :=
  (π _).toAddMonoidHom.comp <| (TensorAlgebra.ι _).toAddMonoidHom

def lift {R : Type*} [Ring R]
    (e : Additive Kˣ →+ R)
    (he : ∀ ⦃x y : Kˣ⦄, (x : K) + y = 1 → e x * e y = 0) :
    MilnorK K →+* R :=
  RingQuot.lift <| {
    val := TensorAlgebra.lift _ e.toIntLinearMap |>.toRingHom
    property := by rintro _ _ ⟨a,b,h⟩ ; simpa using he h
  }

@[simp]
def lift_comp_ι_apply {R : Type*} [Ring R]
    (e : Additive Kˣ →+ R)
    (he : ∀ ⦃x y : Kˣ⦄, (x : K) + y = 1 → e x * e y = 0)
    (x : Additive Kˣ) :
    (lift e he) (ι _ x) = e x := by
  show RingQuot.lift _ (RingQuot.mkRingHom _ _) = _
  simp

@[simp]
def lift_comp_ι {R : Type*} [Ring R]
    (e : Additive Kˣ →+ R)
    (he : ∀ ⦃x y : Kˣ⦄, (x : K) + y = 1 → e x * e y = 0) :
    (lift e he).toAddMonoidHom.comp (ι _) = e := by
  ext
  simp

def hom_ext {R : Type*} [Ring R]
    (f g : MilnorK K →+* R)
    (h : ∀ x, f (ι _ x) = g (ι _ x)) :
    f = g := by
  apply RingQuot.ringQuot_ext
  apply RingHom.toIntAlgHom_injective
  apply TensorAlgebra.hom_ext
  ext
  apply h

def log (x : Kˣ) : MilnorK K := ι _ <| .ofMul x

@[simp]
lemma log_mul (x y : Kˣ) : log (x * y) = log x + log y :=
  (ι K).map_add _ _

@[simp]
lemma log.map_one : log (1 : Kˣ) = 0 :=
  (ι K).map_zero

@[simp]
lemma log.map_inv (x : Kˣ) : log (x⁻¹) = - (log x) :=
  (ι K).map_neg _

syntax "{" term,+ "}ₘ" : term

macro_rules
  | `({$x:term}ₘ) => `(log $x)
  | `({$x:term, $xs:term,*}ₘ) => `((log $x) * {$xs,*}ₘ)

lemma steinberg_relation (x y : Kˣ) (h : (x : K) + y = 1) : {x,y}ₘ = 0 := by
  dsimp [log, ι]
  rw [← (π K).map_mul, ← (π K).map_zero]
  apply RingQuot.mkRingHom_rel
  exact Rel.mk _ _ h

variable {F : Type*} [Field F]

@[simp]
lemma mul_neg_self (x : Fˣ) : {x, -x}ₘ = 0 := by
  by_cases h : x = 1
  · simp [h]
  · have : (1 : F) - x ≠ 0 := fun c => by
      apply h
      rw [sub_eq_zero] at c
      ext
      exact c.symm
    let y : Fˣ := Units.mk0 _ this
    have : (1 : F) - x⁻¹ ≠ 0 := fun c => by
      apply h
      rw [sub_eq_zero] at c
      simpa using c
    let z : Fˣ := Units.mk0 _ this
    have : {x, -x}ₘ + {x, - y * x⁻¹}ₘ = 0 := by
      rw [← mul_add, ← log_mul]
      apply steinberg_relation
      simp [y]
    calc
      {x, -x}ₘ = -{x, -y * x⁻¹}ₘ := by
        rwa [add_eq_zero_iff_eq_neg] at this
      _ = -{x, z}ₘ := by
        congr 4
        ext
        field_simp [y, z]
      _ = {x⁻¹, z}ₘ := by simp
      _ = 0 := by
        apply steinberg_relation
        simp [z]

lemma mul_self (x : Fˣ) : {x,x}ₘ = {x,-1}ₘ := by
  conv =>
    enter [1, 2, 1]
    rw [show x = (-x) * (-1) by simp]
  rw [log_mul, mul_add, mul_neg_self, zero_add]

lemma mul_symm_eq_neg_mul (x y : Fˣ) : {x,y}ₘ = -{y,x}ₘ := by
  rw [← add_eq_zero_iff_eq_neg]
  calc
    _ = {x,-x}ₘ + {x,y}ₘ + {y,x}ₘ + {y,-y}ₘ := by
      simp only [mul_neg_self, zero_add, add_zero]
    _ = {x,-(x * y)}ₘ + {y,-(x * y)}ₘ := sorry -- simp is way too slow...
    _ = {x * y, - (x * y)}ₘ := sorry
    _ = 0 := mul_neg_self _

end MilnorK
