{-# OPTIONS --cubical #-}
module Prelude where
open import Agda.Builtin.Cubical.Path public
open import Agda.Primitive public
open import Agda.Primitive.Cubical public
  renaming ( primIMin   to _∧_
           ; primIMax   to _∨_
           ; primINeg   to ~_
           ; primComp   to comp
           ; primHComp  to hcomp
           ; primTransp to transp
           ; itIsOne    to 1=1 )
open import Agda.Builtin.Cubical.Sub public
  renaming ( inc        to inS
           ; primSubOut to outS )
open import Agda.Builtin.Sigma public

private
  variable
    ℓ : Level
    𝒻 : I → Level

refl₍_₎ : {A : Set ℓ} (a : A) → a ≡ a
refl₍ a ₎ = λ i → a

refl : {A : Set ℓ} {a : A} → a ≡ a
refl = refl₍ _ ₎

path-syntax = PathP

infix 4 path-syntax
syntax path-syntax A u v = u ≡ v [ A ]

path-over : ∀ {𝔞 𝔟} {A : Set 𝔞} (B : A → Set 𝔟)
  → ∀ {x y} → x ≡ y → B x → B y → Set 𝔟
path-over B p u v = PathP (λ i → B (p i)) u v

infix 4 path-over
syntax path-over B p u v = u ≡ v [ B ↓ p ]

infix 4 _[_↦_]
_[_↦_] : (A : Set ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

-- transp : (A  : ∀ i → Set (𝒻 i))
--          (φ  : I)
--          (u₀ : A i0)
--        → -----------
--                A i1

from-transp : {A : I → Set ℓ} {x : A i0} {y : A i1}
  → transp (λ i → A i) i0 x ≡ y
  → x ≡ y [ A ]
from-transp p = {!!}

-- hcomp : {A  : Set ℓ}
--         {φ  : I}
--         (u  : I → Partial φ A)
--         (u₀ : A [ φ ↦ u i0 ])
--       → ----------------------
--               A [ φ ↦ u i1 ]

-- comp : (A  : ∀ i → Set (𝒻 i))
--        {φ  : I}
--        (u  : I → Partial φ (A i))
--        (u₀ : A i0 [ φ ↦ u i0 ])
--      → --------------------------
--              A i1 [ φ ↦ u i1 ]

-- hfill : {A  : Set ℓ}
--         {φ  : I}
--         (u  : I → Partial φ A)
--         (u₀ : A [ φ ↦ u i0 ])
--       → ----------------------
--         u₀ ≡ hcomp u u₀

hfill : {A  : Set ℓ}
        {φ  : I}
        (u  : I → Partial φ A)
        (u₀ : A [ φ ↦ u i0 ])
      → ----------------------
        I → A
hfill {φ = φ} u u₀ i = hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                                      ; (i = i0) → outS u₀ })
                             (outS u₀)

fill : (A  : ∀ i → Set (𝒻 i))
       {φ  : I}
       (u  : ∀ i → Partial φ (A i))
       (u₀ : A i0 [ φ ↦ u i0 ])
     → ----------------------------
       ∀ i → A i
fill A {φ} u u₀ i = comp (λ j → A (i ∧ j))
                         (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                                  ; (i = i0) → outS u₀ })
                         (outS u₀)

infix 2 Σ-syntax
Σ-syntax : ∀ {𝔞 𝔟} (A : Set 𝔞) (B : A → Set 𝔟) → Set (𝔞 ⊔ 𝔟)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

