{-# OPTIONS --safe  #-}

open import Frame.IFrame
import Frame.CFrame as CF

module Presheaf.Functor.Cover.Strong.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (K   : W → Set)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core K _∈_)
  (CF  : CFrame)
  (Cov : Coverage CF)
  where

open IFrame IF
open CFrame CF
open Coverage Cov renaming (refine-comm-cfamily to family-stable)

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Cover.Base IF CF

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import HEUtil

private
  variable
    w w' w'' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' : Psh

strength[_,_] : (𝒫 𝒬 : Psh) → 𝒫 ×' (𝒞 𝒬) →̇ 𝒞 (𝒫 ×' 𝒬)
strength[ 𝒫 , 𝒬 ] = record
  { fun     = λ p×𝒞q → strength-fun (π₁' .apply p×𝒞q) (π₂' .apply p×𝒞q)
  ; pres-≋  = λ r≋r' → strength-fun-pres-≋ (π₁' .apply-≋ r≋r') (π₂' .apply-≋ r≋r')
  ; natural = λ w p×𝒞q → strength-fun-natural w (π₁' .apply p×𝒞q) (π₂' .apply p×𝒞q)
  }
  where

  strength-fun : 𝒫 ₀ w → 𝒞-Fam 𝒬 w → 𝒞-Fam (𝒫 ×' 𝒬) w
  strength-fun p (elem k f) = elem k λ x → elem (wk[ 𝒫 ] (cfamily k x) p , f x)

  opaque
    strength-fun-pres-≋ : {p p' : 𝒫 ₀ w'} {q q' : 𝒞-Fam 𝒬 w'}
        → p ≋[ 𝒫 ] p' → q 𝒞-≋[ 𝒬 ] q'
        → (strength-fun p q) 𝒞-≋[ 𝒫 ×' 𝒬 ] (strength-fun p' q')
    strength-fun-pres-≋ p≋p' (proof ≡-refl f≋f')
      = proof ≡-refl λ { ≅-refl → proof (wk[ 𝒫 ]-pres-≋ _ p≋p' , f≋f' ≅-refl) }

    strength-fun-natural : (i : w ⊆ w') (x : 𝒫 ₀ w) (q : 𝒞-Fam 𝒬 w)
      →  wk[ 𝒞 (𝒫 ×' 𝒬) ] i (strength-fun x q) ≋[ 𝒞 (𝒫 ×' 𝒬) ] strength-fun (wk[ 𝒫 ] i x) (wk[ 𝒞 𝒬 ] i q)
    strength-fun-natural i x (elem k f) = proof ≡-refl (λ { {u} {p} ≅-refl → proof
      ((let (k' , is')    = refine i k
            (_ , p' , i') = is' p
            open EqReasoning ≋[ 𝒫 ]-setoid in begin
          wk[ 𝒫 ] i' (wk[ 𝒫 ] (cfamily k p') x)
            ≈˘⟨ wk[ 𝒫 ]-pres-trans (cfamily k p') i' x ⟩
          wk[ 𝒫 ] (⊆-trans (cfamily k p') i') x
            ≡⟨ ≡-cong (λ w → wk[ 𝒫 ] w x) (family-stable i k p) ⟩
          wk[ 𝒫 ] (⊆-trans i (cfamily k' p)) x
            ≈⟨ wk[ 𝒫 ]-pres-trans i (cfamily k' p) x ⟩
          wk[ 𝒫 ] (cfamily k' p) (wk[ 𝒫 ] i x)
        ∎)
      , ≋[ 𝒬 ]-refl)})


opaque
  unfolding 𝒞-map_

  strength-natural₁ : (t : 𝒫 →̇ 𝒫') → strength[ 𝒫' , 𝒬 ] ∘' (t ×'-map id') ≈̇ (𝒞-map (t ×'-map id')) ∘' strength[ 𝒫 , 𝒬 ]
  strength-natural₁ {𝒬 = 𝒬} t = proof-≈̇ λ p → proof ≡-refl λ { ≅-refl → proof (t .natural _ _ , ≋[ 𝒬 ]-refl) }

  strength-natural₂ : (t : 𝒬 →̇ 𝒬') → strength[ 𝒫 , 𝒬' ] ∘' (id' ×'-map (𝒞-map t)) ≈̇ (𝒞-map (id' ×'-map t)) ∘' strength[ 𝒫 , 𝒬 ]
  strength-natural₂ {𝒬' = 𝒬'} {𝒫 = 𝒫} t = proof-≈̇ (λ _p → proof ≡-refl λ { ≅-refl → ≋[ 𝒫 ×' 𝒬' ]-refl })

  strength-assoc : 𝒞-map assoc' ∘' strength[ 𝒫 ×' 𝒬  , ℛ ] ≈̇ (strength[ 𝒫 , 𝒬 ×' ℛ ] ∘' (id' ×'-map strength[ 𝒬 , ℛ ]) ∘' assoc')
  strength-assoc {𝒫 = 𝒫} {𝒬 = 𝒬} {ℛ = ℛ} = proof-≈̇ (λ _p → ≋[ 𝒞 (𝒫 ×' (𝒬 ×' ℛ)) ]-refl)

  strength-unit : 𝒞-map π₂' ∘' strength[ ⊤' , 𝒫 ] ≈̇ π₂'
  strength-unit {𝒫} = proof-≈̇ (λ _p → ≋[ 𝒞 𝒫 ]-refl)
