{-# OPTIONS --safe --cubical #-}

open import Cubical.Structures.Group

module Groups.Symmetric.Representable {ℓ} (𝓖 : Group {ℓ}) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Groups.Symmetric
open import Groups.Symmetric.Inclusion 𝓖
open import Cubical.Foundations.Equiv
open import Cubical.Data.Vec
open import Cubical.Foundations.SIP

open group-·syntax 𝓖

Representable : ⟨ SymGroup ⟩ → Type ℓ
Representable f = ∀ x g h → x ≡ g · h → fst f x ≡ fst f g · h

Repr : Type ℓ
Repr = Σ[ f ∈ ⟨ SymGroup ⟩ ] Representable f

-- Representable f is a Set

rep-prop : (f : ⟨ SymGroup ⟩) → isProp (Representable f)
rep-prop f = isPropΠ2 (λ x y → isPropΠ2 λ w z → (group-is-set 𝓖 (fst f x) (fst f y · w)))

repΣ-set : isSet Repr
repΣ-set = isSetΣ (group-is-set SymGroup) λ f → isProp→isSet (rep-prop f)

-- Representable elments are closed under group operations

rep-comp : ∀ (f f′ : ⟨ SymGroup ⟩) → Representable f → Representable f′ → Representable (group-operation SymGroup f f′)
rep-comp f f′ rf rf′ x g h p = rf (fst f′ x) (fst f′ g) h (rf′ x g h p)

rep-id : Representable (group-id SymGroup)
rep-id x g h p = p

rep-inv : (f : ⟨ SymGroup ⟩) → Representable f → Representable (group-inv SymGroup f)
rep-inv (f , finv , ε , η) rf x g h p = η (finv g · h) x (p ∙ cong (_· h) (sym (ε g (finv g) refl)) ∙ sym (rf (finv g · h) (finv g) h refl))

-- and hence form a group

RSymGroup : Group {ℓ}
RSymGroup =
  Repr ,
  (λ where (f , rf) (f′ , rf′) → (group-operation SymGroup f f′) , rep-comp f f′ rf rf′) ,
  (repΣ-set , λ x y z → refl) ,
  ((group-id SymGroup) , rep-id) ,
  (λ where (g , rg) → refl , refl) ,
  (λ where (x , rx) → (group-inv SymGroup x , rep-inv x rx) , sigmaPath→pathSigma _ _ (group-rinv SymGroup x , rep-prop (group-id SymGroup) _ _) , sigmaPath→pathSigma _ _ (group-linv SymGroup x , rep-prop (group-id SymGroup) _ _))

-- Any included element is Representable

inc-rep : ∀ (a : ⟨ 𝓖 ⟩) → Representable (inc a)
inc-rep a x g h p =
  a · x ≡⟨ cong (a ·_) p ⟩
  a · (g · h) ≡⟨ group-assoc 𝓖 a g h ⟩
  (a · g) · h ∎

-- Any Representable is the image of an included element

cancellem : ∀ x y z → z · x ≡ z · y → x ≡ y
cancellem x y z p =
  x              ≡⟨ sym (group-lid 𝓖 x) ⟩
  ₁ · x          ≡⟨ sym (cong (_· x) (group-linv 𝓖 z)) ⟩
  (z ⁻¹ · z) · x ≡⟨ sym (group-assoc 𝓖 (z ⁻¹) z x) ⟩
  z ⁻¹ · (z · x) ≡⟨ cong (z ⁻¹ ·_) p ⟩
  z ⁻¹ · (z · y) ≡⟨ group-assoc 𝓖 (z ⁻¹) z y ⟩
  (z ⁻¹ · z) · y ≡⟨ cong (_· y) (group-linv 𝓖 z) ⟩
  ₁ · y          ≡⟨ group-lid 𝓖 y ⟩
  y ∎

rep-inc : ∀ (f : ⟨ SymGroup ⟩) → Representable f → Σ[ g ∈ ⟨ 𝓖 ⟩ ] f ≡ inc g
rep-inc a@(f , finv , ε , η) rf = (f ₁) , sigmaPath→pathSigma _ _ (i , sigmaPath→pathSigma _ _ (transportRefl finv ∙ ii , sigmaPath→pathSigma _ _ (funExt₃ (λ x y z → group-is-set 𝓖 _ _ _ _) , funExt₃ (λ x y z → group-is-set 𝓖 _ _ _ _))))
  where
    i : (λ x → f x) ≡ (λ x → f ₁ · x)
    i = funExt λ x → rf x ₁ x (sym (group-lid 𝓖 x))

    lem : finv ₁ ≡ (f ₁) ⁻¹
    lem = cancellem (finv ₁) (f ₁ ⁻¹) (f ₁)
      (f ₁ · finv ₁ ≡⟨ sym (rf (finv ₁) ₁ (finv ₁) (sym (group-lid 𝓖 (finv ₁)))) ⟩
       f (finv ₁) ≡⟨ ε ₁ (finv ₁) refl ⟩
       ₁ ≡⟨ sym (group-rinv 𝓖 (f ₁)) ⟩
       f ₁ · f ₁ ⁻¹ ∎)

    ii : (λ x → finv x) ≡ (λ x → (f ₁ ⁻¹) · x)
    ii = funExt λ x → (rep-inv a rf x ₁ x (sym (group-lid 𝓖 x))) ∙ cong (_· x) lem

-- We can now define incᵣ and show it is an equivalence

incᵣ : ⟨ 𝓖 ⟩ → Repr
incᵣ g = inc g , inc-rep g

incᵣ-iso : Iso ⟨ 𝓖 ⟩ Repr
incᵣ-iso .Iso.fun = incᵣ
incᵣ-iso .Iso.inv (f , fr) = fst (rep-inc f fr)
incᵣ-iso .Iso.leftInv g = inc-injective (fst (rep-inc (inc g) (inc-rep g))) g (sym (snd (rep-inc (inc g) (inc-rep g))))
incᵣ-iso .Iso.rightInv (f , fr) = ΣPathP ((sym (snd (rep-inc f fr))) , toPathP (rep-prop f _ _))

incᵣ-equiv : ⟨ 𝓖 ⟩ ≃ Repr
incᵣ-equiv = isoToEquiv incᵣ-iso

-- And show it is a group isomorphism

incᵣ-homo : ∀ g h → incᵣ (g · h) ≡ group-operation RSymGroup (incᵣ g) (incᵣ h)
incᵣ-homo g h = ΣPathP (inc-homo g h , toPathP (rep-prop (group-operation SymGroup (inc g) (inc h)) _ _))

incᵣ-group-iso : 𝓖 ≃[ group-iso ] RSymGroup
incᵣ-group-iso = incᵣ-equiv , λ where (g ∷ h ∷ []) → incᵣ-homo g h

-- And so the two groups are equal

inc≡ : 𝓖 ≡ RSymGroup
inc≡ = equivFun (GroupPath 𝓖 RSymGroup) incᵣ-group-iso
