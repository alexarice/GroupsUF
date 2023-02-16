We show that there is an inclusion from any group into into the Symmetric group of its underlying set.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

open import Cubical.Algebra.Group

module Groups.Symmetric.Inclusion {ℓ} (𝓖 : Group ℓ) where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Groups.Function.Inverse
open import Groups.Symmetric

open GroupStr (𝓖 .snd)
```

</details>

```agda
SymGroup : Group ℓ
SymGroup = Symmetric-Group ⟨ 𝓖 ⟩ (isSetGroup 𝓖)
```

The inclusion takes `g` to the function `λ x → g · x` with inverse `λ x → g ⁻¹ · x`

```agda
inc : ⟨ 𝓖 ⟩ → ⟨ SymGroup ⟩
inc g = (λ x → g · x) , (λ x → inv g · x) , i , ii
  where
    i : (b x : ⟨ 𝓖 ⟩) → x ≡ inv g · b → g · x ≡ b
    i b x p =
      g · x          ≡⟨ cong (g ·_) p ⟩
      g · (inv g · b) ≡⟨ ·Assoc g (inv g) b ⟩
      (g · inv g) · b ≡⟨ cong (_· b) (·InvR g) ⟩
      1g · b          ≡⟨ ·IdL b ⟩
      b ∎

    ii : (a y : ⟨ 𝓖 ⟩) → y ≡ g · a → inv g · y ≡ a
    ii a y p =
      inv g · y       ≡⟨ cong (inv g ·_) p ⟩
      inv g · (g · a) ≡⟨ ·Assoc (inv g) g a ⟩
      (inv g · g) · a ≡⟨ cong (_· a) (·InvL g) ⟩
      1g · a          ≡⟨ ·IdL a ⟩
      a ∎
```

## Inclusion properties

The inclusion can be shown to be injective and a group homomorphism.

```agda
inc-injective : (x y : ⟨ 𝓖 ⟩) → inc x ≡ inc y → x ≡ y
inc-injective x y p =
  x     ≡⟨ sym (·IdR x) ⟩
  x · 1g ≡⟨ cong (λ a → fst a 1g) p ⟩
  y · 1g ≡⟨ ·IdR y ⟩
  y ∎

open GroupStr (SymGroup .snd) using () renaming (_·_ to _·′_; 1g to 1gs; inv to invs)
inc-homo : (x y : ⟨ 𝓖 ⟩) → inc (x · y) ≡ (inc x) ·′ (inc y)
inc-homo x y = inverse-equality-lemma _ _ (isSetGroup 𝓖) (isSetGroup 𝓖)
  λ g → sym (·Assoc x y g)

inc-pres1 : inc 1g ≡ 1gs
inc-pres1 = inverse-equality-lemma (inc 1g) 1gs (isSetGroup 𝓖) (isSetGroup 𝓖) ·IdL

inc-pres-inv : (g : ⟨ 𝓖 ⟩) → inc (inv g) ≡ invs (inc g)
inc-pres-inv g = inverse-equality-lemma (inc (inv g)) (invs (inc g)) (isSetGroup 𝓖) (isSetGroup 𝓖) (λ x → refl)
```
