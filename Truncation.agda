{-# OPTIONS --cubical #-}
module Truncation where
open import Prelude
open import Groupoid
open import HLevel

private
  variable
    ℓ : Level

data ∥_∥ (A : Set ℓ) : Set ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) (p q : x ≡ y) → p ≡ q

rec : {A : Set ℓ} {C : Set ℓ} → is-set C → (A → C) → ∥ A ∥ → C
rec C-is-set f ∣ x ∣ = f x
rec C-is-set f (squash x y p q j i) = C-is-set (rec C-is-set f x) _ (cong (rec C-is-set f) p) (cong (rec C-is-set f) q) j i

elim : {A : Set ℓ} {C : ∥ A ∥ → Set ℓ}
     → (s : (x : ∥ A ∥) → is-set (C x))
     → (f : (a : A) → C ∣ a ∣)
     → (x : ∥ A ∥) → C x
elim s f ∣ x ∣ = f x
elim s f (squash x y p q j i) = {!!}
