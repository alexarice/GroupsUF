This file defines the notion of a representable element of the symmetric group. Representable elements should (and do) correspond to elements of the symmetric group in the image of the inclusion `⟨ 𝓖 ⟩ → SymGroup ⟨ 𝓖 ⟩`. However they must be defined in a different way to preserve the strict associativity and unitality.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

open import Cubical.Algebra.Group

module Groups.Symmetric.Representable {ℓ} (𝓖 : Group ℓ) where

open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv
open import Groups.Function.Inverse
open import Groups.Symmetric
open import Groups.Symmetric.Inclusion 𝓖

open GroupStr (𝓖 .snd) using (_·_;1g;inv)
open GroupStr (SymGroup .snd) using () renaming (_·_ to _·′_; 1g to 1gs; inv to _⁻¹)
open GroupStr hiding (_·_;1g;inv)
```

</details>

We define `Representable` as follows. A similar trick to the one used for inverses is used to ensure strict associativity and unitality is maintained. Without this trick the definition says that a function `f` is representable if `f (g + h) ≡ f g + h` for all `g h ∈ ⟨ 𝓖 ⟩`.

```agda
Representable : (f : ⟨ 𝓖 ⟩ → ⟨ 𝓖 ⟩) → Type ℓ
Representable f = ∀ x g h → x ≡ g · h → f x ≡ f g · h

Repr : Type ℓ
Repr = Σ[ f ∈ ⟨ SymGroup ⟩ ] Representable (fst f) × Representable (fst (snd f))
```

## Set properties

`Representable` is a Prop and so `Repr` is a set.

```agda

rep-prop : (f : ⟨ 𝓖 ⟩ → ⟨ 𝓖 ⟩) → isProp (Representable f)
rep-prop f = isPropΠ2 (λ x y →
             isPropΠ2 λ w z → (isSetGroup 𝓖 (f x) (f y · w)))

repΣ-set : isSet Repr
repΣ-set = isSetΣ (isSetGroup SymGroup) λ f → isProp→isSet (isProp× (rep-prop (fst f)) (rep-prop (fst (snd f))))
```

As `Representable f` is a prop we can prove that `Repr`s are equal if the underlying permutations are.

```agda
repr-equality : (f g : Repr) → fst f ≡ fst g → f ≡ g
repr-equality (f , fr) (g , gr) p =
  ΣPathP (p , (isProp→PathP (λ i → isProp× (rep-prop (fst (p i))) (rep-prop (fst (snd (p i))))) fr gr))
```

## Group properties

Representable elements are closed under group operations

```agda
repr-comp : ∀ (f g : ⟨ 𝓖 ⟩ → ⟨ 𝓖 ⟩) → Representable f → Representable g → Representable (λ x → f (g x))
repr-comp f g rf rg x f′ g′ p = rf (g x) (g f′) g′ (rg x f′ g′ p)

repr-id : Representable (λ x → x)
repr-id x g h p = p

repr-inv : ∀ (f : ⟨ SymGroup ⟩) → Representable (fst f) → Representable (fst (snd f))
repr-inv (f , finv , ε , η) rf x g h p = η (finv g · h) x (
  x              ≡⟨ p ⟩
  g · h          ≡⟨ cong (_· h) (sym (ε g (finv g) refl)) ⟩
  f (finv g) · h ≡⟨ sym (rf (finv g · h) (finv g) h refl) ⟩
  f (finv g · h) ∎)

Repr-comp : ∀ (f f′ : Repr) → Repr
Repr-comp (f , rf , rf′) (g , rg , rg′) = f ·′ g , repr-comp (fst f) (fst g) rf rg , repr-comp (fst (snd g)) (fst (snd f)) rg′ rf′

Repr-id : Repr
Repr-id = 1gs , repr-id , repr-id

Repr-inv : (f : Repr) → Repr
Repr-inv (a@(f , finv , ε , η) , rf , rf′) = a ⁻¹ , rf′ , rf
```

Associativity and Unitality still hold by definition

```agda
Repr-assoc : (f g h : Repr) → Repr-comp f (Repr-comp g h) ≡ Repr-comp (Repr-comp f g) h
Repr-assoc f g h = refl

Repr-lid : (f : Repr) → Repr-comp Repr-id f ≡ f
Repr-lid f = refl

Repr-rid : (f : Repr) → Repr-comp f Repr-id ≡ f
Repr-rid f = refl
```

We can prove the invertibility properties

```agda
Repr-inv-left : (f : Repr) → Repr-comp (Repr-inv f) f ≡ Repr-id
Repr-inv-left f = repr-equality (Repr-comp (Repr-inv f) f) Repr-id
                               (·InvL (SymGroup .snd) (fst f))

Repr-inv-right : (f : Repr) → Repr-comp f (Repr-inv f) ≡ Repr-id
Repr-inv-right f = repr-equality (Repr-comp f (Repr-inv f)) Repr-id
                                (·InvR (SymGroup .snd) (fst f))
```

and the following invertibility property holds definitionally

```agda
Repr-inv-comp : (f g : Repr) → Repr-inv (Repr-comp f g) ≡ Repr-comp (Repr-inv g) (Repr-inv f)
Repr-inv-comp f g = refl
```

and hence representable elements of the symmetric group themselves form a group.

```agda
RSymGroup : Group ℓ
RSymGroup = makeGroup
  Repr-id
  Repr-comp
  Repr-inv
  repΣ-set
  Repr-assoc
  Repr-lid
  Repr-rid
  Repr-inv-right
  Repr-inv-left

open GroupStr (RSymGroup .snd) using () renaming (_·_ to _*_; 1g to 1gr; inv to invᵣ)
```

## Isomorphism

As stated above, an element is representable if and only if it is in the image of the inclusion homomorphism.

We first have that every included element is representable.

```agda
inc-rep : ∀ (a : ⟨ 𝓖 ⟩) → Representable (fst (inc a))
inc-rep a x g h p =
  a · x ≡⟨ cong (a ·_) p ⟩
  a · (g · h) ≡⟨ ·Assoc (𝓖 .snd) a g h ⟩
  (a · g) · h ∎
```
and that any representable element is the image of an included element
```agda
Repr-inc : ∀ (f : Repr) → Σ[ g ∈ ⟨ 𝓖 ⟩ ] inc g ≡ fst f
Repr-inc (a@(f , rest) , rf , rf′) = (f 1g) ,
  inverse-equality-lemma (inc (f 1g)) a (isSetGroup 𝓖) (isSetGroup 𝓖)
                         λ x → sym (rf x 1g x (sym (·IdL (𝓖 .snd) x)))
```

This allows us to define `incᵣ`

```agda
incᵣ : ⟨ 𝓖 ⟩ → Repr
incᵣ g = inc g , inc-rep g , repr-inv (inc g) (inc-rep g)
```

and show that it is an equivalence.

```agda
open Iso

incᵣ-iso : Iso ⟨ 𝓖 ⟩ Repr
incᵣ-iso .fun = incᵣ
incᵣ-iso .inv f = fst (Repr-inc f)
incᵣ-iso .leftInv g =
  inc-injective (fst (Repr-inc (incᵣ g))) g (snd (Repr-inc (incᵣ g)))
incᵣ-iso .rightInv f =
  repr-equality (incᵣ (fst (Repr-inc f))) f (snd (Repr-inc f))

incᵣ-equiv : ⟨ 𝓖 ⟩ ≃ Repr
incᵣ-equiv = isoToEquiv incᵣ-iso
```

Further it is also a group homomorphism.

```agda
incᵣ-homo : ∀ g h → incᵣ (g · h) ≡ incᵣ g * incᵣ h
incᵣ-homo g h =
  repr-equality (incᵣ (g · h)) (incᵣ g * incᵣ h) (inc-homo g h)

incᵣ-pres1 : incᵣ-equiv .fst 1g ≡ 1gr
incᵣ-pres1 = repr-equality (incᵣ-equiv .fst 1g) 1gr inc-pres1

incᵣ-presinv : (x : ⟨ 𝓖 ⟩) → incᵣ-equiv .fst (GroupStr.inv (snd 𝓖) x) ≡ invᵣ (incᵣ-equiv .fst x)
incᵣ-presinv x = repr-equality (incᵣ-equiv .fst (GroupStr.inv (snd 𝓖) x)) (invᵣ (incᵣ-equiv .fst x)) (inc-pres-inv x)

incᵣ-group-iso : GroupEquiv 𝓖 RSymGroup
incᵣ-group-iso = incᵣ-equiv , record { pres· = incᵣ-homo ; pres1 = incᵣ-pres1 ; presinv = incᵣ-presinv }
```

Using the structure identity principle, `⟨ 𝓖 ⟩` and `RSymgroup ⟨ 𝓖 ⟩` are actually equal.

```agda
inc≡ : 𝓖 ≡ RSymGroup
inc≡ = equivFun (GroupPath 𝓖 RSymGroup) incᵣ-group-iso
```
