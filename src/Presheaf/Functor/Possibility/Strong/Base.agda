{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.FDFrame as FDF

module Presheaf.Functor.Possibility.Strong.Base
  {W   : Set}
  {_⊑_ : (w w' : W) → Set}
  {IF  : IFrame W _⊑_}
  {_R_ : (w v : W) → Set}
  (let open FDF IF _R_)
  {DF  : DFrame}
  (let open Definitions DF)
  (IDF : InclusiveDFrame)
  where

open DFrame DF
open InclusiveDFrame IDF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' : Psh

strength[_,_] : (𝒫 𝒬 : Psh) → 𝒫 ×' (◇ 𝒬) →̇ ◇ (𝒫 ×' 𝒬)
strength[ 𝒫 , 𝒬 ] = record
  { fun     = λ p×◇q → strength-fun (π₁' .apply p×◇q) (π₂' .apply p×◇q)
  ; pres-≋  = λ r≋r' → strength-fun-pres-≋ (π₁' .apply-≋ r≋r') (π₂' .apply-≋ r≋r')
  ; natural = λ w p×◇q → strength-fun-natural w (π₁' .apply p×◇q) (π₂' .apply p×◇q)
  }
  where

  strength-fun : 𝒫 ₀ w → ◇-Fam 𝒬 w → ◇-Fam (𝒫 ×' 𝒬) w
  strength-fun p (elem (Δ , r , q)) = elem (Δ , r , elem (wk[ 𝒫 ] (R-to-⊑ r) p , q))

  opaque
    strength-fun-pres-≋ : {p p' : 𝒫 ₀ w'} {q q' : ◇-Fam 𝒬 w'}
        → p ≋[ 𝒫 ] p' → q ◇-≋[ 𝒬 ] q'
        → (strength-fun p q) ◇-≋[ 𝒫 ×' 𝒬 ] (strength-fun p' q')
    strength-fun-pres-≋ p≋p' (proof (refl , refl , q≋q')) = proof (refl , refl , proof (wk[ 𝒫 ]-pres-≋ _ p≋p' , q≋q'))

    strength-fun-natural : (i : w ⊑ w') (p : 𝒫 ₀ w) (q : ◇-Fam 𝒬 w)
      →  wk[ ◇ (𝒫 ×' 𝒬) ] i (strength-fun p q) ≋[ ◇ (𝒫 ×' 𝒬) ] strength-fun (wk[ 𝒫 ] i p) (wk[ ◇ 𝒬 ] i q)
    strength-fun-natural w p q = let open EqReasoning ≋[ 𝒫 ]-setoid in
      proof (refl , (refl , (proof
        ((begin
          wk[ 𝒫 ] (factor⊑ w _) (wk[ 𝒫 ] (R-to-⊑ _) p)
            ≈˘⟨ wk[ 𝒫 ]-pres-trans (R-to-⊑ _) (factor⊑ w _) p ⟩
          wk[ 𝒫 ] (⊑-trans (R-to-⊑ _) (factor⊑ w _)) p
            ≡˘⟨ cong (λ w → wk[ 𝒫 ] w p) (factor-pres-R-to-⊑ w _) ⟩
          wk[ 𝒫 ] (⊑-trans w (R-to-⊑ (factorR w _))) p
            ≈⟨  wk[ 𝒫 ]-pres-trans w (R-to-⊑ (factorR w _)) p ⟩
          wk[ 𝒫 ] (R-to-⊑ (factorR w _)) (wk[ 𝒫 ] w p)
           ∎)
        , ≋[ 𝒬 ]-refl))))

opaque
  unfolding ◇-map_
  
  strength-natural₁ : (t : 𝒫 →̇ 𝒫') → strength[ 𝒫' , 𝒬 ] ∘' (t ×'-map id') ≈̇ (◇-map (t ×'-map id')) ∘' strength[ 𝒫 , 𝒬 ]
  strength-natural₁ {𝒬 = 𝒬} t = proof-≈̇ (λ _p → proof (refl , refl , proof (t .natural _ _ , ≋[ 𝒬 ]-refl)))

  strength-natural₂ : (t : 𝒬 →̇ 𝒬') → strength[ 𝒫 , 𝒬' ] ∘' (id' ×'-map (◇-map t)) ≈̇ (◇-map (id' ×'-map t)) ∘' strength[ 𝒫 , 𝒬 ]
  strength-natural₂ {𝒬' = 𝒬'} {𝒫 = 𝒫} t = proof-≈̇ (λ _p → proof (refl , refl , ≋[ 𝒫 ×' 𝒬' ]-refl))

  strength-assoc : ◇-map assoc' ∘' strength[ 𝒫 ×' 𝒬  , ℛ ] ≈̇ (strength[ 𝒫 , 𝒬 ×' ℛ ] ∘' (id' ×'-map strength[ 𝒬 , ℛ ]) ∘' assoc')
  strength-assoc {𝒫 = 𝒫} {𝒬 = 𝒬} {ℛ = ℛ} = proof-≈̇ (λ _p → ≋[ ◇ (𝒫 ×' (𝒬 ×' ℛ)) ]-refl)

  strength-unit : ◇-map π₂' ∘' strength[ ⊤' , 𝒫 ] ≈̇ π₂'
  strength-unit {𝒫} = proof-≈̇ (λ _p → ≋[ ◇ 𝒫 ]-refl)
