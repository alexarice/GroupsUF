We show that there is an inclusion from any group into into the Symmetric group of its underlying set.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

open import Cubical.Structures.Group

module Groups.Symmetric.Inclusion {ℓ} (𝓖 : Group {ℓ}) where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv
open import Groups.Function.Inverse
open import Groups.Symmetric

open group-·syntax 𝓖
```

</details>

```agda
SymGroup : Group
SymGroup = Symmetric-Group ⟨ 𝓖 ⟩ (group-is-set 𝓖)
```

The inclusion takes `g` to the function `λ x → g · x` with inverse `λ x → g ⁻¹ · x`
```agda
inc : ⟨ 𝓖 ⟩ → ⟨ SymGroup ⟩
inc g = (λ x → g · x) , (λ x → g ⁻¹ · x) , i , ii
  where
    i : (b x : ⟨ 𝓖 ⟩) → x ≡ g ⁻¹ · b → g · x ≡ b
    i b x p =
      g · x          ≡⟨ cong (g ·_) p ⟩
      g · (g ⁻¹ · b) ≡⟨ group-assoc 𝓖 g (g ⁻¹) b ⟩
      (g · g ⁻¹) · b ≡⟨ cong (_· b) (group-rinv 𝓖 g) ⟩
      ₁ · b          ≡⟨ group-lid 𝓖 b ⟩
      b ∎

    ii : (a y : ⟨ 𝓖 ⟩) → y ≡ g · a → g ⁻¹ · y ≡ a
    ii a y p =
      g ⁻¹ · y       ≡⟨ cong (g ⁻¹ ·_) p ⟩
      g ⁻¹ · (g · a) ≡⟨ group-assoc 𝓖 (g ⁻¹) g a ⟩
      (g ⁻¹ · g) · a ≡⟨ cong (_· a) (group-linv 𝓖 g) ⟩
      ₁ · a          ≡⟨ group-lid 𝓖 a ⟩
      a ∎
```

## Inclusion properties

The inclusion can be shown to be injective and a group homomorphism.

```agda
inc-injective : (x y : ⟨ 𝓖 ⟩) → inc x ≡ inc y → x ≡ y
inc-injective x y p =
  x ≡⟨ sym (group-rid 𝓖 x) ⟩
  x · ₁ ≡⟨ cong (λ a → fst a ₁) p ⟩
  y · ₁ ≡⟨ group-rid 𝓖 y ⟩
  y ∎

inc-homo : (x y : ⟨ 𝓖 ⟩) → inc (x · y) ≡ group-operation (SymGroup) (inc x) (inc y)
inc-homo x y = inverse-equality-lemma _ _ (group-is-set 𝓖) (group-is-set 𝓖) λ g → sym (group-assoc 𝓖 x y g)
```
