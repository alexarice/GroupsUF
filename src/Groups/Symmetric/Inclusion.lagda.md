We show that there is an inclusion from any group into into the Symmetric group of its underlying set.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

open import Cubical.Algebra.Group

module Groups.Symmetric.Inclusion {ℓ} (𝓖 : Group {ℓ}) where

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
SymGroup : Group
SymGroup = Symmetric-Group ⟨ 𝓖 ⟩ (isSetGroup 𝓖)
```

The inclusion takes `g` to the function `λ x → g · x` with inverse `λ x → g ⁻¹ · x`

```agda
inc : ⟨ 𝓖 ⟩ → ⟨ SymGroup ⟩
inc g = (λ x → g + x) , (λ x → - g + x) , i , ii
  where
    i : (b x : ⟨ 𝓖 ⟩) → x ≡ - g + b → g + x ≡ b
    i b x p =
      g + x          ≡⟨ cong (g +_) p ⟩
      g + (- g + b) ≡⟨ assoc g (- g) b ⟩
      (g + - g) + b ≡⟨ cong (_+ b) (invr g) ⟩
      0g + b          ≡⟨ lid b ⟩
      b ∎

    ii : (a y : ⟨ 𝓖 ⟩) → y ≡ g + a → - g + y ≡ a
    ii a y p =
      - g + y       ≡⟨ cong (- g +_) p ⟩
      - g + (g + a) ≡⟨ assoc (- g) g a ⟩
      (- g + g) + a ≡⟨ cong (_+ a) (invl g) ⟩
      0g + a          ≡⟨ lid a ⟩
      a ∎
```

## Inclusion properties

The inclusion can be shown to be injective and a group homomorphism.

```agda
inc-injective : (x y : ⟨ 𝓖 ⟩) → inc x ≡ inc y → x ≡ y
inc-injective x y p =
  x     ≡⟨ sym (rid x) ⟩
  x + 0g ≡⟨ cong (λ a → fst a 0g) p ⟩
  y + 0g ≡⟨ rid y ⟩
  y ∎

open GroupStr (SymGroup .snd) using () renaming (_+_ to _·_)
inc-homo : (x y : ⟨ 𝓖 ⟩) → inc (x + y) ≡ (inc x) · (inc y)
inc-homo x y = inverse-equality-lemma _ _ (isSetGroup 𝓖) (isSetGroup 𝓖)
                                      λ g → sym (assoc x y g)
```
