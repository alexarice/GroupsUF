This file defines invertible functions in a way that makes them strictly associative and unital.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --cubical --safe #-}

module Groups.Function.Inverse where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ ℓ′ ℓ″ ℓ‴ : Level
    A : Type ℓ
    B : Type ℓ′
    C : Type ℓ″
    D : Type ℓ‴
```

</details>

The definition is given as an iterated Sigma type to make various proofs easier.

```agda
Inverse : (A : Type ℓ) (B : Type ℓ′) → Type (ℓ-max ℓ ℓ′)
Inverse A B = Σ[ ↑ ∈ (A → B) ] Σ[ ↓ ∈ (B → A) ]
              (∀ b x → x ≡ ↓ b → ↑ x ≡ b) ×
              (∀ a y → y ≡ ↑ a → ↓ y ≡ a)
```

## Set Properties

We can show this is a set using standard functions from the Cubical library.

```agda
isSetInv : isSet A → isSet B → isSet (Inverse A B)
isSetInv isSetA isSetB =
  isSetΣ (isSetΠ λ x → isSetB) λ f →
    isSetΣ (isSetΠ λ x → isSetA) λ g →
      isSet× (isSetΠ3 λ x y z → isProp→isSet (isSetB (f y) x))
             (isSetΠ3 λ x y z → isProp→isSet (isSetA (g y) x))
```

We next prove a small lemma that says that inverses between sets are the same if their underlying (forward) functions are the same.

```agda
inverse-equality-lemma : (f g : Inverse A B) → isSet A → isSet B →
                         ((x : A) → fst f x ≡ fst g x) → f ≡ g
inverse-equality-lemma {A = A} {B = B} (f , finv , εf , ηf)
                                       (g , ginv , εg , ηg)
                                       isSetA isSetB p =
  ΣPathP (funExt p , toPathP (
  ΣPathP (funExt lem , toPathP (
  ΣPathP (funExt₃ (λ x y z → isSetB _ _ _ _) ,
          funExt₃ (λ x y z → isSetA _ _ _ _))))))
  where
    lem : (x : B) → transp (λ i → A) i0 (finv (transp (λ j → B) i0 x)) ≡ ginv x
    lem x =
      transp (λ i → A) i0 (finv (transp (λ j → B) i0 x))
         ≡⟨ transportRefl (finv (transp (λ j → B) i0 x)) ⟩
      finv (transp (λ j → B) i0 x) ≡⟨ cong finv (transportRefl x) ⟩
      finv x                       ≡⟨ cong finv (sym (εg x (ginv x) refl)) ⟩
      finv (g (ginv x))            ≡⟨ ηf (ginv x) (g (ginv x)) (sym (p (ginv x))) ⟩
      ginv x ∎
```

## Group Properties

We are able to define composition and inverses as follows:

```agda
infixr 30 _∘_
_∘_ : Inverse B C → Inverse A B → Inverse A C
_∘_ (f , g , p , q) (f′ , g′ , p′ , q′) =
  (λ x → f (f′ x)) ,
  (λ x → g′ (g x)) ,
  (λ b x r → p b (f′ x) (p′ (g b) x r)) ,
  λ a y r → q′ a (g y) (q (f′ a) y r)

id-inv : Inverse A A
id-inv = (λ x → x) , (λ x → x) , (λ b x p → p) , λ a y p → p
```

As wanted, associativity and unitality hold definitionally.

```agda
inv-comp-assoc : ∀ (f : Inverse C D) (g : Inverse B C) (h : Inverse A B) →
                   f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
inv-comp-assoc f g h = refl

id-unit-left : (f : Inverse A B) → id-inv ∘ f ≡ f
id-unit-left f = refl

id-unit-right : (f : Inverse A B) → f ∘ id-inv ≡ f
id-unit-right f = refl
```

The remainder of the properties also hold.

```agda
inv-inv : (f : Inverse A B) → Inverse B A
inv-inv (f , g , p , q) = g , f , q , p

inv-inv-left : isSet A → (f : Inverse A B) → inv-inv f ∘ f ≡ id-inv
inv-inv-left isSetA f@(↑ , ↓ , ε , η) =
  inverse-equality-lemma (inv-inv f ∘ f) id-inv isSetA isSetA λ x → η x (↑ x) refl

inv-inv-right : isSet B → (f : Inverse A B) → f ∘ inv-inv f ≡ id-inv
inv-inv-right isSetB f@(↑ , ↓ , ε , η) =
  inverse-equality-lemma (f ∘ inv-inv f) id-inv isSetB isSetB λ x → ε x (↓ x) refl
```
