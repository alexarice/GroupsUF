{-# OPTIONS --safe --cubical #-}

open import Cubical.Structures.Group

module Groups.Symmetric.Representable {ℓ} (𝓖 : Group {ℓ}) where

open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv
open import Function.Inverse
open import Groups.Symmetric
open import Groups.Symmetric.Inclusion 𝓖

open group-·syntax 𝓖
open group-operation-syntax

Representable : ⟨ SymGroup ⟩ → Type ℓ
Representable f = ∀ x g h → x ≡ g · h → fst f x ≡ fst f g · h

Repr : Type ℓ
Repr = Σ[ f ∈ ⟨ SymGroup ⟩ ] Representable f

-- Representable is a Prop and so Repr is a set

rep-prop : (f : ⟨ SymGroup ⟩) → isProp (Representable f)
rep-prop f = isPropΠ2 (λ x y → isPropΠ2 λ w z → (group-is-set 𝓖 (fst f x) (fst f y · w)))

repΣ-set : isSet Repr
repΣ-set = isSetΣ (group-is-set SymGroup) λ f → isProp→isSet (rep-prop f)

-- Representable elments are closed under group operations

rep-comp : ∀ (f f′ : Repr) → Repr
rep-comp (f , rf) (f′ , rf′) = f ·⟨ SymGroup ⟩ f′ , λ x g h p → rf (fst f′ x) (fst f′ g) h (rf′ x g h p)

rep-id : Repr
rep-id = group-id SymGroup , λ x g h p → p

rep-inv : (f : Repr) → Repr
rep-inv (a@(f , finv , ε , η) , rf) = (group-inv SymGroup a) ,
  λ x g h p → η (finv g · h) x
   (x              ≡⟨ p ⟩
    g · h          ≡⟨ cong (_· h) (sym (ε g (finv g) refl)) ⟩
    f (finv g) · h ≡⟨ sym (rf (finv g · h) (finv g) h refl) ⟩
    f (finv g · h) ∎)

-- Associativity and Unitality still hold by definition

rep-assoc : (f g h : Repr) → rep-comp f (rep-comp g h) ≡ rep-comp (rep-comp f g) h
rep-assoc f g h = refl

rep-lid : (f : Repr) → rep-comp rep-id f ≡ f
rep-lid f = refl

rep-rid : (f : Repr) → rep-comp f rep-id ≡ f
rep-rid f = refl

-- Reprs are equal if the underlying object is

repr-equality : (f g : Repr) → fst f ≡ fst g → f ≡ g
repr-equality (f , fr) (g , gr) p = ΣPathP (p , (isProp→PathP (λ i → rep-prop (p i)) fr gr))

-- And so the inverses work as expected

rep-inv-left : (f : Repr) → rep-comp (rep-inv f) f ≡ rep-id
rep-inv-left f = repr-equality (rep-comp (rep-inv f) f) rep-id (group-linv SymGroup (fst f))

rep-inv-right : (f : Repr) → rep-comp f (rep-inv f) ≡ rep-id
rep-inv-right f = repr-equality (rep-comp f (rep-inv f)) rep-id (group-rinv SymGroup (fst f))

-- and hence form a group

RSymGroup : Group {ℓ}
RSymGroup =
  Repr ,
  rep-comp ,
  (repΣ-set , rep-assoc) ,
  rep-id ,
  (λ g → rep-lid g , rep-rid g) ,
  (λ x → (rep-inv x , rep-inv-right x , rep-inv-left x))

-- Any included element is Representable

inc-rep : ∀ (a : ⟨ 𝓖 ⟩) → Representable (inc a)
inc-rep a x g h p =
  a · x ≡⟨ cong (a ·_) p ⟩
  a · (g · h) ≡⟨ group-assoc 𝓖 a g h ⟩
  (a · g) · h ∎

-- Any Representable is the image of an included element

rep-inc : ∀ (f : Repr) → Σ[ g ∈ ⟨ 𝓖 ⟩ ] inc g ≡ fst f
rep-inc (a@(f , rest) , rf) = (f ₁) ,
  inverse-equality-lemma (inc (f ₁)) a (group-is-set 𝓖) (group-is-set 𝓖) λ x → sym (rf x ₁ x (sym (group-lid 𝓖 x)))

-- We can now define incᵣ and show it is an equivalence

incᵣ : ⟨ 𝓖 ⟩ → Repr
incᵣ g = inc g , inc-rep g

incᵣ-iso : Iso ⟨ 𝓖 ⟩ Repr
incᵣ-iso .Iso.fun = incᵣ
incᵣ-iso .Iso.inv f = fst (rep-inc f)
incᵣ-iso .Iso.leftInv g = inc-injective (fst (rep-inc (incᵣ g))) g (snd (rep-inc (incᵣ g)))
incᵣ-iso .Iso.rightInv f = repr-equality (incᵣ (fst (rep-inc f))) f (snd (rep-inc f))

incᵣ-equiv : ⟨ 𝓖 ⟩ ≃ Repr
incᵣ-equiv = isoToEquiv incᵣ-iso

-- And show it is a group isomorphism

incᵣ-homo : ∀ g h → incᵣ (g · h) ≡ incᵣ g ·⟨ RSymGroup ⟩ (incᵣ h)
incᵣ-homo g h = repr-equality (incᵣ (g · h)) (incᵣ g ·⟨ RSymGroup ⟩ incᵣ h) (inc-homo g h)

incᵣ-group-iso : 𝓖 ≃[ group-iso ] RSymGroup
incᵣ-group-iso = incᵣ-equiv , λ where (g ∷ h ∷ []) → incᵣ-homo g h

-- And so the two groups are equal

inc≡ : 𝓖 ≡ RSymGroup
inc≡ = equivFun (GroupPath 𝓖 RSymGroup) incᵣ-group-iso
