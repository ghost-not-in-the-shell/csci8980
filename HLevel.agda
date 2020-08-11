{-# OPTIONS --cubical #-}
module HLevel where
open import Prelude
open import Groupoid
open import Agda.Builtin.Nat renaming (Nat to ℕ)

private
  variable
    ℓ : Level

is-contr : Set ℓ → Set ℓ
is-contr A = Σ[ x ∈ A ] ∀ y → x ≡ y

is-prop : Set ℓ → Set ℓ
is-prop A = (x y : A) → x ≡ y

is-set : Set ℓ → Set ℓ
is-set A = (x y : A) (p q : x ≡ y) → p ≡ q

_has-level_ : Set ℓ → ℕ → Set ℓ
A has-level 0 = is-contr A
A has-level 1 = is-prop  A
A has-level (suc (suc n)) = (x y : A) → (x ≡ y) has-level (suc n)

private
  variable
    𝔞 𝔟 : Level

is-contrΔ : {A : Set 𝔞} → (A → Set 𝔟) → Set (𝔞 ⊔ 𝔟)
is-contrΔ B = ∀ {a} → Σ[ b ∈ B a ] ∀ {a′} (b′ : B a′) (p : a ≡ a′) → b ≡ b′ [ B ↓ p ]

is-propΔ : {A : Set 𝔞} → (A → Set 𝔟) → Set (𝔞 ⊔ 𝔟)
is-propΔ B = ∀ {a₀ a₁} (x : B a₀) (y : B a₁) (p : a₀ ≡ a₁) → x ≡ y [ B ↓ p ]

is-setΔ : {A : Set 𝔞} → (A → Set 𝔟) → Set (𝔞 ⊔ 𝔟)
is-setΔ B = ∀ {a₀ a₁} (x : B a₀) (y : B a₁) {p₀ p₁ : a₀ ≡ a₁} (α : x ≡ y [ B ↓ p₀ ]) (β : x ≡ y [ B ↓ p₁ ]) (ρ : p₀ ≡ p₁) → α ≡ β [ (λ - → x ≡ y [ B ↓ - ]) ↓ ρ ]

_has-levelΔ_ : {A : Set 𝔞} → (A → Set 𝔟) → ℕ → Set (𝔞 ⊔ 𝔟)
B has-levelΔ 0 = is-contrΔ B
B has-levelΔ 1 = is-propΔ  B
B has-levelΔ (suc (suc n)) = ∀ {a₀ a₁} (x : B a₀) (y : B a₁) → (λ (p : a₀ ≡ a₁) → x ≡ y [ B ↓ p ]) has-levelΔ (suc n)
