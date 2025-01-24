{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

module Presheaf.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  where

open IFrame IF

open import Level using (0ℓ)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

infixr 19 _∘_
infix  18 _→̇_ _≈̇_

private
  variable
    w w' w'' : W
    v v' v'' : W

record Psh : Set₁ where
  no-eta-equality
  field
    -- setoids
    Fam       : (w : W) → Set
    _≋_       : (x y : Fam w) → Set -- type \~~~
    ≋-equiv   : ∀ (w : W) → IsEquivalence {A = Fam w} _≋_

    -- setoid morphisms
    wk        : (i : w ⊆ v) → (x : Fam w) → Fam v
    wk-pres-≋ : ∀ (i : w ⊆ v) {x y : Fam w} (x≋y : x ≋ y) → wk i x ≋ wk i y

    -- functoriality
    wk-pres-refl  : ∀ (x : Fam w) → wk ⊆-refl x ≋ x
    wk-pres-trans : ∀ (i : w ⊆ w') (i' : w' ⊆ w'') (x : Fam w) → wk (⊆-trans i i') x ≋ wk i' (wk i x)

  infix 19 Fam

  Fam-setoid : {w : W} → Setoid _ _
  Fam-setoid {w} = record
    { Carrier       = Fam w
    ; _≈_           = _≋_
    ; isEquivalence = ≋-equiv w
    }

  wk-pres-≡-≋ : ∀ {i i' : w ⊆ v} (i≡i' : i ≡ i') {x y : Fam w} (x≋y : x ≋ y) → wk i x ≋ wk i' y
  wk-pres-≡-≋ {i = i} {.i} ≡-refl = wk-pres-≋ i

  module _ {w : W} where
    open IsEquivalence (≋-equiv w) public
      using ()
      renaming
        ( refl      to ≋-refl
        ; sym       to ≋-sym
        ; trans     to ≋-trans
        ; reflexive to ≋-reflexive
        )

  ≋-reflexive˘ : ∀ {x y : Fam w} → y ≡ x → x ≋ y
  ≋-reflexive˘ ≡-refl = ≋-refl

-- open Psh {{...}} using (_≋_; ≋-refl; ≋-sym; ≋-trans; wk) public
-- ≋-refl  = λ {𝒫} {w} {p}         → 𝒫 .Psh.≋-refl {w} {p}
-- ≋-sym   = λ {𝒫} {w} {p} {q}     → 𝒫 .Psh.≋-sym {w} {p} {q}
-- ≋-trans = λ {𝒫} {w} {p} {q} {r} → 𝒫 .Psh.≋-trans {w} {p} {q} {r}
open Psh public
  using ()
  renaming
    ( Fam           to _₀_
    ; Fam-setoid    to ≋[_]-setoid
    ; ≋-refl        to ≋[_]-refl
    ; ≋-sym         to ≋[_]-sym
    ; ≋-trans       to ≋[_]-trans
    ; ≋-reflexive   to ≋[_]-reflexive
    ; ≋-reflexive˘  to ≋[_]-reflexive˘
    ; wk            to wk[_]
    ; wk-pres-≋     to wk[_]-pres-≋
    ; wk-pres-≡-≋   to wk[_]-pres-≡-≋
    ; wk-pres-refl  to wk[_]-pres-refl
    ; wk-pres-trans to wk[_]-pres-trans
    )

private
  variable
    𝒫 𝒫' : Psh -- type \McP
    𝒬 𝒬' : Psh -- type \McQ
    ℛ ℛ' : Psh -- type \McR
    𝒮 𝒮' : Psh -- type \McS

≋[]-syntax : (𝒫 : Psh) → (x y : 𝒫 ₀ w) → Set
≋[]-syntax 𝒫 = 𝒫 .Psh._≋_

syntax ≋[]-syntax 𝒫 x y = x ≋[ 𝒫 ] y

Pres-≋ : (𝒫 𝒬 : Psh) → ({w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → Set
Pres-≋ 𝒫 𝒬 f = {w : W} {p p' : 𝒫 ₀ w} (p≋p' : p ≋[ 𝒫 ] p') → f p ≋[ 𝒬 ] f p'

Natural : (𝒫 𝒬 : Psh) → ({w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → Set
Natural 𝒫 𝒬 f = {w v : W} (i : w ⊆ v) (p : 𝒫 ₀ w) → wk[ 𝒬 ] i (f p) ≋[ 𝒬 ] f (wk[ 𝒫 ] i p)

record _→̇_ (𝒫 𝒬 : Psh) : Set where -- type \-> \^.
  no-eta-equality
  field
    fun     : (p : 𝒫 ₀ w) → 𝒬 ₀ w
    pres-≋  : Pres-≋ 𝒫 𝒬 fun
    natural : Natural 𝒫 𝒬 fun

open _→̇_ using (natural) renaming (fun to apply; pres-≋ to apply-≋) public

Hom : Psh → Psh → Set
Hom 𝒫 𝒬 = 𝒫 →̇ 𝒬

record _≈̇_ (φ ψ : 𝒫 →̇ 𝒬) : Set where -- type \~~ \^.
  no-eta-equality
  field
    proof : ∀ (p : 𝒫 ₀ w) → φ .apply p ≋[ 𝒬 ] ψ .apply p

  apply-sq : ∀ {p p' : 𝒫 ₀ w} → p ≋[ 𝒫 ] p' → φ .apply p ≋[ 𝒬 ] ψ .apply p' -- XXX: rename
  apply-sq {p = p} {p'} p≋p' = let open EqReasoning ≋[ 𝒬 ]-setoid in begin
    φ .apply p   ≈⟨ φ .apply-≋ p≋p' ⟩
    φ .apply p'  ≈⟨ proof p' ⟩
    ψ .apply p'  ∎

open _≈̇_ using (apply-sq) renaming (proof to apply-≋) public

private
  variable
    φ φ' : 𝒫 →̇ 𝒬
    ψ ψ' : 𝒫 →̇ 𝒬
    ω ω' : 𝒫 →̇ 𝒬

module _ {𝒫 𝒬 : Psh} where
  opaque
    ≈̇-refl : Reflexive {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-refl = record { proof = λ {_} _ → ≋[ 𝒬 ]-refl }

    ≈̇-sym : Symmetric {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-sym φ≋φ' = record { proof = λ {_} p → ≋[ 𝒬 ]-sym (φ≋φ' ._≈̇_.proof p) }

    ≈̇-trans : Transitive {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-trans φ≋ψ ψ≋ω = record { proof = λ {_} p → ≋[ 𝒬 ]-trans (φ≋ψ ._≈̇_.proof p) (ψ≋ω ._≈̇_.proof p) }

    ≈̇-equiv : IsEquivalence {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-equiv = record
      { refl  = ≈̇-refl
      ; sym   = ≈̇-sym
      ; trans = ≈̇-trans
      }

module _ (𝒫 𝒬 : Psh) where
  →̇-setoid : Setoid 0ℓ 0ℓ
  →̇-setoid = record
    { Carrier       = 𝒫 →̇ 𝒬
    ; _≈_           = _≈̇_
    ; isEquivalence = ≈̇-equiv
    }

_∘_ : (ψ : 𝒬 →̇ ℛ) → (φ : 𝒫 →̇ 𝒬) → 𝒫 →̇ ℛ
_∘_ {𝒬} {ℛ} {𝒫} ψ φ = record
  { fun     = ∘-fun
  ; pres-≋  = ∘-fun-pres-≋
  ; natural = ∘-fun-natural
  }
  where
    ∘-fun : 𝒫 ₀ w → ℛ ₀ w
    ∘-fun = λ p → ψ .apply (φ .apply p)

    opaque
      ∘-fun-pres-≋ : Pres-≋ 𝒫 ℛ (λ p → ψ .apply (φ .apply p))
      ∘-fun-pres-≋ p≋p' = ψ .apply-≋ (φ .apply-≋ p≋p')

      ∘-fun-natural : Natural 𝒫 ℛ ∘-fun
      ∘-fun-natural i p = let open EqReasoning ≋[ ℛ ]-setoid in begin
        wk[ ℛ ] i (ψ .apply (φ .apply p))  ≈⟨ ψ .natural _ _ ⟩
        ψ .apply (wk[ 𝒬 ] i (φ .apply p))  ≈⟨ ψ .apply-≋ (φ .natural _ _) ⟩
        ψ .apply (φ .apply (wk[ 𝒫 ] i p))  ∎

_[_]' = _∘_

opaque
  ∘-pres-≈̇ : ψ ≈̇ ψ' → φ ≈̇ φ' → ψ ∘ φ ≈̇ ψ' ∘ φ'
  ∘-pres-≈̇ ψ≈̇ψ' φ≈̇φ' = record { proof = λ p → apply-sq ψ≈̇ψ' (φ≈̇φ' .apply-≋ p) }

  ∘-pres-≈̇-left : ∀ (_ : ψ ≈̇ ψ') (φ : 𝒫 →̇ 𝒬) → ψ ∘ φ ≈̇ ψ' ∘ φ
  ∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {x = φ})

  ∘-pres-≈̇-right : ∀ (ψ : 𝒬 →̇ ℛ) (_ : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
  ∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {x = ψ}) φ≈̇φ'

  ∘-assoc : ∀ (ω : ℛ →̇ 𝒮) (ψ : 𝒬 →̇ ℛ) (φ : 𝒫 →̇ 𝒬) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ
  ∘-assoc {_} {ℛ} ω ψ φ = record { proof = λ p → ≋[ ℛ ]-refl }

id'[_] : (𝒫 : Psh) → 𝒫 →̇ 𝒫
id'[_] 𝒫 = record
  { fun     = λ p → p
  ; pres-≋  = λ p≋p' → p≋p'
  ; natural = λ _ _ → ≋[ 𝒫 ]-refl
  }

id' = λ {𝒫} → id'[ 𝒫 ]

opaque
  ∘-unit-left : ∀ {𝒫 : Psh} (𝒬 : Psh) (φ : 𝒫 →̇ 𝒬) → id'[ 𝒬 ] ∘ φ ≈̇ φ
  ∘-unit-left 𝒬 _ = record { proof = λ p → ≋[ 𝒬 ]-refl }

  ∘-unit-right : ∀ (𝒫 : Psh) {𝒬 : Psh} (φ : 𝒫 →̇ 𝒬) → φ ∘ id'[ 𝒫 ] ≈̇ φ
  ∘-unit-right _ {𝒬} _ = record { proof = λ p → ≋[ 𝒬 ]-refl }
