This file defines the notion of a representable element of the symmetric group. Representable elements should (and do) correspond to elements of the symmetric group in the image of the inclusion `⟨ 𝓖 ⟩ → SymGroup ⟨ 𝓖 ⟩`. However they must be defined in a different way to preserve the strict associativity and unitality.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

open import Cubical.Algebra.Group

module Groups.Symmetric.Representable {ℓ} (𝓖 : Group ℓ) where

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
Representable : ⟨ SymGroup ⟩ → Type ℓ
Representable f = ∀ x g h → x ≡ g · h → fst f x ≡ fst f g · h

Repr : Type ℓ
Repr = Σ[ f ∈ ⟨ SymGroup ⟩ ] Representable f
```

## Set properties

`Representable` is a Prop and so `Repr` is a set.

```agda
rep-prop : (f : ⟨ SymGroup ⟩) → isProp (Representable f)
rep-prop f = isPropΠ2 (λ x y →
             isPropΠ2 λ w z → (isSetGroup 𝓖 (fst f x) (fst f y · w)))

repΣ-set : isSet Repr
repΣ-set = isSetΣ (isSetGroup SymGroup) λ f → isProp→isSet (rep-prop f)
```

As `Representable f` is a prop we can prove that `Repr`s are equal if the underlying permutations are.

```agda
repr-equality : (f g : Repr) → fst f ≡ fst g → f ≡ g
repr-equality (f , fr) (g , gr) p =
  ΣPathP (p , (isProp→PathP (λ i → rep-prop (p i)) fr gr))
```

## Group properties

Representable elements are closed under group operations

```agda
rep-comp : ∀ (f f′ : Repr) → Repr
rep-comp (f , rf) (f′ , rf′) = f ·′ f′ ,
                               λ x g h p → rf (fst f′ x) (fst f′ g) h (rf′ x g h p)

rep-id : Repr
rep-id = 1gs , λ x g h p → p

rep-inv : (f : Repr) → Repr
rep-inv (a@(f , finv , ε , η) , rf) = a ⁻¹ ,
  λ x g h p → η (finv g · h) x
   (x              ≡⟨ p ⟩
    g · h          ≡⟨ cong (_· h) (sym (ε g (finv g) refl)) ⟩
    f (finv g) · h ≡⟨ sym (rf (finv g · h) (finv g) h refl) ⟩
    f (finv g · h) ∎)
```

Associativity and Unitality still hold by definition

```agda
rep-assoc : (f g h : Repr) → rep-comp f (rep-comp g h) ≡ rep-comp (rep-comp f g) h
rep-assoc f g h = refl

rep-lid : (f : Repr) → rep-comp rep-id f ≡ f
rep-lid f = refl

rep-rid : (f : Repr) → rep-comp f rep-id ≡ f
rep-rid f = refl
```

We can prove the invertibility properties

```agda
rep-inv-left : (f : Repr) → rep-comp (rep-inv f) f ≡ rep-id
rep-inv-left f = repr-equality (rep-comp (rep-inv f) f) rep-id
                               (invl (SymGroup .snd) (fst f))

rep-inv-right : (f : Repr) → rep-comp f (rep-inv f) ≡ rep-id
rep-inv-right f = repr-equality (rep-comp f (rep-inv f)) rep-id
                                (invr (SymGroup .snd) (fst f))
```

and hence representable elements of the symmetric group themselves form a group.

```agda
RSymGroup : Group ℓ
RSymGroup = makeGroup
  rep-id
  rep-comp
  rep-inv
  repΣ-set
  rep-assoc
  rep-lid
  rep-rid
  rep-inv-right
  rep-inv-left

open GroupStr (RSymGroup .snd) using () renaming (_·_ to _*_; 1g to 1gr; inv to invᵣ)
```

## Isomorphism

As stated above, an element is representable if and only if it is in the image of the inclusion homomorphism.

We first have that every included element is representable.

```agda
inc-rep : ∀ (a : ⟨ 𝓖 ⟩) → Representable (inc a)
inc-rep a x g h p =
  a · x ≡⟨ cong (a ·_) p ⟩
  a · (g · h) ≡⟨ assoc (𝓖 .snd) a g h ⟩
  (a · g) · h ∎
```
and that any representable element is the image of an included element
```agda
rep-inc : ∀ (f : Repr) → Σ[ g ∈ ⟨ 𝓖 ⟩ ] inc g ≡ fst f
rep-inc (a@(f , rest) , rf) = (f 1g) ,
  inverse-equality-lemma (inc (f 1g)) a (isSetGroup 𝓖) (isSetGroup 𝓖)
                         λ x → sym (rf x 1g x (sym (lid (𝓖 .snd) x)))
```

This allows us to define `incᵣ`

```agda
incᵣ : ⟨ 𝓖 ⟩ → Repr
incᵣ g = inc g , inc-rep g
```

and show that it is an equivalence.

```agda
open Iso

incᵣ-iso : Iso ⟨ 𝓖 ⟩ Repr
incᵣ-iso .fun = incᵣ
incᵣ-iso .inv f = fst (rep-inc f)
incᵣ-iso .leftInv g =
  inc-injective (fst (rep-inc (incᵣ g))) g (snd (rep-inc (incᵣ g)))
incᵣ-iso .rightInv f =
  repr-equality (incᵣ (fst (rep-inc f))) f (snd (rep-inc f))

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
