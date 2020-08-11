{-# OPTIONS --cubical #-}
module Groupoid where
open import Prelude

private
  variable
    𝔞 𝔟 : Level
    A : Set 𝔞
    B : A → Set 𝔟
    a b c d x y : A

sym : a ≡ b → b ≡ a
sym p = λ i → p (~ i)

infix 6 _⁻¹
_⁻¹ = sym

--     a ∙ ∙ ∙ > d
--     ^         ^
-- p⁻¹ |         | r
--     |         |
--     b - - - > c
--         q
_∙∙_∙∙_ : a ≡ b → b ≡ c → c ≡ d → a ≡ d
p ∙∙ q ∙∙ r = λ i → hcomp (λ j → λ { (i = i0) → p (~ j)
                                   ; (i = i1) → r j })
                          (q i)

_↑↑_↑↑_ : (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → q ≡ p ∙∙ q ∙∙ r [ (λ j → p (~ j) ≡ r j) ]
p ↑↑ q ↑↑ r = λ j i → hfill (λ j → λ { (i = i0) → p (~ j)
                                     ; (i = i1) → r j })
                            (inS (q i)) j

infixr 5 _∙_
_∙_ : a ≡ b → b ≡ c → a ≡ c
p ∙ q = refl ∙∙ p ∙∙ q

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _≡⟨_⟩_
  infix  3 _∎

  begin_ : a ≡ b → a ≡ b
  begin p = p

  _≡⟨_⟩_ : a → a ≡ b → b ≡ c → a ≡ c
  a ≡⟨ p ⟩ q = p ∙ q

  _∎ : (a : A) → a ≡ a
  a ∎ = refl

cong : (f : (x : A) → B x)
       (p : x ≡ y)
     → -----------------------------
       f x ≡ f y [ B ↓ p ]
cong f p = λ i → f (p i)
{-# INLINE cong #-}

infixl 4 _<$>_
_<$>_ = cong

infixl 4 _<*>_
_<*>_ : {f g : (x : A) → B x}
        (p   : f ≡ g)
        (q   : x ≡ y)
      → -----------------------------
        f x ≡ g y [ B ↓ q ]
p <*> q = λ i → p i (q i)

transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

subst : (B : A → Set 𝔟) → x ≡ y → B x → B y
subst P p u = transport (cong P p) u

infix 4 _∼_
_∼_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : A → Set 𝔟} (f g : (x : A) → B x) → Set (𝔞 ⊔ 𝔟)
f ∼ g = ∀ x → f x ≡ g x

funext : {f : (x : A) → B x}
         {g : (x : A) → B x}
       → f ∼ g
       → f ≡ g
funext p i x = p x i

⁻¹-involutive : (p : a ≡ b) → p ⁻¹ ⁻¹ ≡ p
⁻¹-involutive p = refl

∙-unitˡ : (p : a ≡ b) → refl ∙ p ≡ p
∙-unitˡ {a = a} {b = b} p = λ j i → hcomp (λ k → λ { (i = i0) → a
                                                   ; (i = i1) → p (j ∨ k)
                                                   ; (j = i0) → (refl ↑↑ refl ↑↑ p) k i
                                                   ; (j = i1) → p i })
                                          (p (i ∧ j))

-- ∙-unitʳ : (p : a ≡ b) → p ∙ refl ≡ p
-- ∙-unitʳ {a = a} {b = b} p = sym (refl ↑↑ p ↑↑ refl)

∙-unitʳ : (p : a ≡ b) → p ∙ refl ≡ p
∙-unitʳ {a = a} {b = b} p = λ j i → hcomp (λ k → λ { (i = i0) → a
                                                   ; (i = i1) → b
                                                   ; (j = i0) → (refl ↑↑ p ↑↑ refl) k i
                                                   ; (j = i1) → p i })
                                           (p i)

⁻¹-unit : refl₍ a ₎ ⁻¹ ≡ refl
⁻¹-unit {a = a} = λ j i → a

∙-invˡ : (p : a ≡ b) → p ⁻¹ ∙ p ≡ refl
∙-invˡ {a = a} {b = b} p = λ j i → hcomp (λ k → λ { (i = i0) → b
                                                  ; (i = i1) → p (j ∨ k)
                                                  ; (j = i0) → (refl ↑↑ p ⁻¹ ↑↑ p) k i
                                                  ; (j = i1) → b })
                                         (p (~ i ∨ j))

∙-invˡ′ : (p : a ≡ b) → p ⁻¹ ∙ p ≡ refl
∙-invˡ′ {a = a} {b = b} p = λ j i → hcomp (λ k → λ { (i = i0) → b
                                                   ; (i = i1) → p k
                                                   ; (j = i0) → (refl ↑↑ p ⁻¹ ↑↑ p) k i

                                                   ; (j = i1) → p (~ i ∨ k) })
                                          (p (~ i))

∙-invʳ : (p : a ≡ b) → p ∙ p ⁻¹ ≡ refl
∙-invʳ {a = a} {b = b} p = ∙-invˡ (p ⁻¹)

3-out-of-4 : (left : a ≡ b) (bottom : b ≡ c) (right : c ≡ d) {top₁ top₂ : a ≡ d}
             (square₁ : bottom ≡ top₁ [ (λ j → left (~ j) ≡ right j) ])
             (square₂ : bottom ≡ top₂ [ (λ j → left (~ j) ≡ right j) ])
           → top₁ ≡ top₂
3-out-of-4 p q r square₁ square₂ =
  λ j i → hcomp (λ k → λ { (i = i0) → p (~ k)
                         ; (i = i1) → r k
                         ; (j = i0) → square₁ k i
                         ; (j = i1) → square₂ k i })
                (q i)

∙-assoc : (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc {a = a} p q r = 3-out-of-4 refl p (q ∙ r) square₁ square₂
  where square₁ : p ≡ (p ∙ q) ∙ r [ (λ j → a ≡ (q ∙ r) j) ]
        square₁ = λ j i → hcomp (λ k → λ { (i = i0) → a
                                         ; (i = i1) → (refl ↑↑ q ↑↑ r) k j
                                         ; (j = i0) → p i
                                         ; (j = i1) → (refl ↑↑ p ∙ q ↑↑ r) k i })
                                ((refl ↑↑ p ↑↑ q) j i)

        square₂ : p ≡ p ∙ (q ∙ r) [ (λ j → a ≡ (q ∙ r) j) ]
        square₂ = refl ↑↑ p ↑↑ (q ∙ r)
