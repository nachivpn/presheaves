{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.DFrame as KDF

module Presheaf.Functor.Lax
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open KDF IF _R_)
  (DF   : DFrame)
  where

open DFrame DF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF public

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' : W
    𝒫 𝒬 ℛ   : Psh

-- type \bigcirc or \ci5 for ◯
record ◯-Fam (𝒫 : Psh) (w : W) : Set where
  constructor elem
  field
      fun     : {w' : W} → (i : w ⊆ w') → ◇-Fam 𝒫 w'
      natural : (i : w ⊆ w') (i' : w' ⊆ w'')
        → wk[ ◇ 𝒫 ] i' (fun i) ≋[ ◇ 𝒫 ] fun (⊆-trans i i')

open ◯-Fam renaming (fun to apply-◯) public

record _◯-≋_ {𝒫 : Psh} {w : W} (f f' : ◯-Fam 𝒫 w) : Set where
    constructor proof
    field
      pw : {w' : W} → (i : w ⊆ w') → (f .apply-◯ i) ◇-≋[ 𝒫 ] (f' .apply-◯ i)

open _◯-≋_ using (pw) public

◯-≋-refl : Reflexive (_◯-≋_ {𝒫} {w})
◯-≋-refl = proof λ _i → ◇-≋-refl

◯-≋-sym : Symmetric (_◯-≋_ {𝒫} {w})
◯-≋-sym = λ f≋f' → proof λ i → ◇-≋-sym (f≋f' .pw i)

◯-≋-trans : Transitive (_◯-≋_ {𝒫} {w})
◯-≋-trans = λ f≋f' f'≋f'' → proof λ i → ◇-≋-trans (f≋f' .pw i) (f'≋f'' .pw i)

≡-to-◯-≋ : {x y : ◯-Fam 𝒫 w} → x ≡ y → x ◯-≋ y
≡-to-◯-≋ ≡-refl = ◯-≋-refl

◯-≋[]-syn : (𝒫 : Psh) → (x y : ◯-Fam 𝒫 w) → Set
◯-≋[]-syn {w = w} 𝒫 = _◯-≋_ {𝒫} {w}

syntax ◯-≋[]-syn 𝒫 x y = x ◯-≋[ 𝒫 ] y

---------------------
-- ◯ 𝒫 is a presheaf
---------------------

◯_ : (𝒫 : Psh) → Psh
◯ 𝒫 = record
  { Fam           = ◯-Fam 𝒫
  ; _≋_           = _◯-≋_
  ; ≋-equiv       = ≋-equiv
  ; wk            = wk
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where

    ≋-equiv : (w : W) → IsEquivalence (_◯-≋_ {𝒫} {w})
    ≋-equiv = λ w → record
      { refl  = ◯-≋-refl
      ; sym   = ◯-≋-sym
      ; trans = ◯-≋-trans
      }

    wk : w ⊆ w' → ◯-Fam 𝒫 w → ◯-Fam 𝒫 w'
    wk i f = record
      { fun = λ i' → f .apply-◯ (⊆-trans i i')
      ; natural = λ i' i'' → let open EqReasoning ≋[ ◇ 𝒫 ]-setoid in begin
        wk[ ◇ 𝒫 ] i'' (f .apply-◯ (⊆-trans i i'))
          ≈⟨ f .natural (⊆-trans i i') i'' ⟩
        f .apply-◯ (⊆-trans (⊆-trans i i') i'')
          ≡⟨ cong (f .apply-◯) (⊆-trans-assoc i i' i'') ⟩
        f .apply-◯ (⊆-trans i (⊆-trans i' i'')) ∎ }

    opaque
      wk-pres-≋ : (i : w ⊆ w') {f f' : ◯-Fam 𝒫 w} (f≋f' : f ◯-≋ f') → wk i f ◯-≋ wk i f'
      wk-pres-≋ i f≋f' = proof λ i' → f≋f' .pw (⊆-trans i i')

      wk-pres-refl : (f : ◯-Fam 𝒫 w) → wk ⊆-refl f ◯-≋ f
      wk-pres-refl f = proof (λ i → ≡-to-◇-≋ (cong (f .apply-◯) (⊆-trans-unit-left i)))

      wk-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (f : ◯-Fam 𝒫 w) → wk (⊆-trans i i') f ◯-≋ wk i' (wk i f)
      wk-pres-trans i i' f = proof (λ i'' → ≡-to-◇-≋ (cong (f .apply-◯) (⊆-trans-assoc i i' i'')))

---------------------------
-- ◯ is a presheaf functor
---------------------------

◯-map_ : (t : 𝒫 →̇ 𝒬) → (◯ 𝒫 →̇ ◯ 𝒬)
◯-map_ {𝒫} {𝒬} = λ t → record
    { fun     = λ p → record
      { fun     = λ i → (◇-map t) .apply (p .apply-◯ i)
      ; natural = λ i i' → let open EqReasoning ≋[ ◇ 𝒬 ]-setoid in begin
         wk[ ◇ 𝒬 ] i' ((◇-map t) .apply (p .apply-◯ i))
          ≈⟨ (◇-map t) .natural i' (p .apply-◯ i) ⟩
        (◇-map t) .apply (wk[ ◇ 𝒫 ] i' (p .apply-◯ i))
          ≈⟨ (◇-map t) .apply-≋ (p .natural i i') ⟩
        (◇-map t) .apply (p .apply-◯ (⊆-trans i i')) ∎ }
    ; pres-≋  = λ p≋p' → proof λ i → (◇-map t) .apply-≋ (p≋p' .pw i)
    ; natural = λ i p → proof λ i' → ≋[ ◇ 𝒬 ]-refl
    }

opaque
  ◯-map-pres-≈̇ : {t t' : 𝒫 →̇  𝒬} → t ≈̇ t' → ◯-map t ≈̇ ◯-map t'
  ◯-map-pres-≈̇ t≈̇t' = record { proof = λ p → proof λ i → ◇-map-fun-pres-≈̇ t≈̇t' (p .apply-◯ i) }

  ◯-map-pres-id : ◯-map id'[ 𝒫 ] ≈̇ id'
  ◯-map-pres-id = record { proof = λ _p → proof λ _i → ◇-≋-refl }

  ◯-map-pres-∘ : (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◯-map (t' ∘ t) ≈̇ ◯-map t' ∘ ◯-map t
  ◯-map-pres-∘ _t' _t = record { proof = λ _p → proof λ i → ◇-≋-refl }

-------------------------------------------------------
-- Presheaf functors ◯ and ◇ are naturally isomorphic
-------------------------------------------------------

module ◯≅◇ where

  ◯≅◇-forth[_] : (𝒫 : Psh) → ◯ 𝒫 →̇ ◇ 𝒫
  ◯≅◇-forth[ 𝒫 ] = record
    { fun     = λ ◯p → ◯p .apply-◯ ⊆-refl
    ; pres-≋  = λ ◯p≋◯p' → ◯p≋◯p' .pw ⊆-refl
    ; natural = λ i p → let open EqReasoning ≋[ ◇ 𝒫 ]-setoid in
      begin
      wk[ ◇ 𝒫 ] i (p .apply-◯ ⊆-refl)
        ≈⟨ p .natural ⊆-refl i ⟩
      p .apply-◯ (⊆-trans ⊆-refl i)
        ≡⟨ cong (p .apply-◯) (≡-trans (⊆-trans-unit-left _) (≡-sym (⊆-trans-unit-right _))) ⟩
      p .apply-◯ (⊆-trans i ⊆-refl)
        ≡⟨⟩
      wk[ ◯ 𝒫 ] i p .apply-◯ ⊆-refl ∎ }

  -- ◯≅◇-forth[_] is a natural transformation (in the category of presheaf functors)
  ◯≅◇-forth-nat : (f : 𝒫 →̇ 𝒬) → ◯≅◇-forth[ 𝒬 ] ∘ ◯-map f ≈̇  (◇-map f) ∘ ◯≅◇-forth[ 𝒫 ]
  ◯≅◇-forth-nat {𝒫} {𝒬} f = record { proof = λ p → ◇-≋-refl }

  ◯≅◇-back[_] : (𝒫 : Psh) → ◇ 𝒫 →̇ ◯ 𝒫
  ◯≅◇-back[ 𝒫 ] = record
    { fun     = λ ◇p → record
      { fun     = λ i → wk[ ◇ 𝒫 ] i ◇p
      ; natural = λ i i' → ≋[ ◇ 𝒫 ]-sym (wk[ ◇ 𝒫 ]-pres-trans i i' ◇p) }
    ; pres-≋  = λ ◇p≋◇p' → proof (λ i → wk[ ◇ 𝒫 ]-pres-≋ i ◇p≋◇p')
    ; natural = λ i ◇p → proof (λ i' → wk[ ◇ 𝒫 ]-pres-trans i i' ◇p) }

  -- ◯≅◇-back[_] is a natural transformation (in the category of presheaf functors)
  ◯≅◇-back-nat : (f : 𝒫 →̇ 𝒬) → ◯≅◇-back[ 𝒬 ] ∘ ◇-map f ≈̇  (◯-map f) ∘ ◯≅◇-back[ 𝒫 ]
  ◯≅◇-back-nat {𝒫} {𝒬} f = record
    { proof = λ p → proof λ i → let open EqReasoning ≋[ ◇ 𝒬 ]-setoid in begin
      wk[ ◇ 𝒬 ] i ((◇-map f) .apply p)
        ≈⟨ (◇-map f) .natural i p ⟩
      (◇-map f) .apply (wk[ ◇ 𝒫 ] i p) ∎
    }

  --
  -- ◯≅◇-forth and ◯≅◇-back are component-wise isomorphic
  --

  ◯≅◇-back-left-inverse : ◯≅◇-back[ 𝒫 ] ∘ ◯≅◇-forth[ 𝒫 ] ≈̇ id'[ ◯ 𝒫 ]
  ◯≅◇-back-left-inverse {𝒫} = record
    { proof = λ p → proof λ i → let open EqReasoning ≋[ ◇ 𝒫 ]-setoid in begin
        wk[ ◇ 𝒫 ] i (p .apply-◯ ⊆-refl)
          ≈⟨ ◯≅◇-forth[ 𝒫 ] .natural i p ⟩
        p .apply-◯ (⊆-trans i ⊆-refl)
          ≡⟨ cong (p .apply-◯) (⊆-trans-unit-right i) ⟩
        p .apply-◯ i ∎
    }


  ◯≅◇-back-right-inverse : ◯≅◇-forth[ 𝒫 ] ∘ ◯≅◇-back[ 𝒫 ] ≈̇ id'[ ◇ 𝒫 ]
  ◯≅◇-back-right-inverse {𝒫} = record { proof = wk[ ◇ 𝒫 ]-pres-refl }
