{-# OPTIONS --cubical --safe #-}

module Function.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Core.Primitives

private
  variable
    ℓ ℓ′ ℓ″ ℓ‴ : Level
    A : Type ℓ
    B : Type ℓ′
    C : Type ℓ″
    D : Type ℓ‴

Inverse : (A : Type ℓ) (B : Type ℓ′) → Type (ℓ-max ℓ ℓ′)
Inverse A B = Σ[ ↑ ∈ (A → B) ] Σ[ ↓ ∈ (B → A) ] (∀ b x → x ≡ ↓ b → ↑ x ≡ b) × (∀ a y → y ≡ ↑ a → ↓ y ≡ a)


isSetInv : isSet A → isSet B → isSet (Inverse A B)
isSetInv isSetA isSetB =
  isSetΣ (isSetΠ λ x → isSetB) λ f →
    isSetΣ (isSetΠ (λ x → isSetA)) λ g →
      isSet× (isSetΠ2 (λ x y → isSetΠ (λ z → isOfHLevelSuc 1 (isSetB (f y) x))))
        (isSetΠ2 (λ x y → isSetΠ (λ z → isOfHLevelSuc 1 (isSetA (g y) x))))

infixr 30 _∘_
_∘_ : Inverse B C → Inverse A B → Inverse A C
_∘_ (f , g , p , q) (f′ , g′ , p′ , q′) =
  (λ x → f (f′ x)) ,
  (λ x → g′ (g x)) ,
  (λ b x r → p b (f′ x) (p′ (g b) x r)) ,
  λ a y r → q′ a (g y) (q (f′ a) y r)

inv-comp-assoc : ∀ (f : Inverse C D) (g : Inverse B C) (h : Inverse A B) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
inv-comp-assoc f g h = refl

id-inv : Inverse A A
id-inv = (λ x → x) , (λ x → x) , (λ b x p → p) , λ a y p → p

id-unit-left : (f : Inverse A B) → id-inv ∘ f ≡ f
id-unit-left f = refl

id-unit-right : (f : Inverse A B) → f ∘ id-inv ≡ f
id-unit-right f = refl

inv-inv : (f : Inverse A B) → Inverse B A
inv-inv (f , g , p , q) = g , f , q , p

inv-inv-left : isSet A → (f : Inverse A B) → inv-inv f ∘ f ≡ id-inv
inv-inv-left isSetA (↑ , ↓ , ε , η) =  sigmaPath→pathSigma _ _
  ((funExt (λ x → η _ _ refl)) , sigmaPath→pathSigma _ _ (funExt (λ x → (transportRefl _) ∙ η _ _ (cong ↑ (transportRefl x))) , sigmaPath→pathSigma _ _ (funExt₃ (λ x y z → isSetA _ _ _ _) , funExt₃ (λ x y z → isSetA _ _ _ _))))

inv-inv-right : isSet B → (f : Inverse A B) → f ∘ inv-inv f ≡ id-inv
inv-inv-right isSetB (↑ , ↓ , ε , η) = sigmaPath→pathSigma _ _
  ((funExt (λ x → ε _ _ refl)) , sigmaPath→pathSigma _ _ ((funExt (λ x → (transportRefl _) ∙ ε _ _ (cong ↓ (transportRefl x)))) , sigmaPath→pathSigma _ _ (funExt₃ (λ x y z → isSetB _ _ _ _) , funExt₃ (λ x y z → isSetB _ _ _ _))))
