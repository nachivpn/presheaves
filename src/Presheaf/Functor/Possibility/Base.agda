{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.FDFrame as FDF

module Presheaf.Functor.Possibility.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open FDF IF _R_)
  (DF   : DFrame)
  where

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF

open DFrame DF

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' v v' v''     : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

-- type \di2 for ◇
record ◇-Fam (𝒫 : Psh) (w : W) : Set where
  constructor elem
  field
    triple : w R-× (𝒫 ₀_)

open ◇-Fam public

record _◇-≋_ {𝒫 : Psh} {w : W} (x y : ◇-Fam 𝒫 w) : Set where
  constructor proof
  field
    pw : let (v , r , p) = x .triple ; (v' , r' , p') = y. triple
      in ∃ λ v≡v' → subst (_ R_) v≡v' r ≡ r' × subst (𝒫 ₀_) v≡v' p ≋[ 𝒫 ] p'

open _◇-≋_ public

◇-≋-refl : Reflexive (_◇-≋_ {𝒫} {w})
◇-≋-refl {𝒫} = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-refl)

◇-≋-sym : Symmetric (_◇-≋_ {𝒫} {w})
◇-≋-sym {𝒫} (proof (≡-refl , ≡-refl , p)) = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-sym p)

◇-≋-trans : Transitive (_◇-≋_ {𝒫} {w})
◇-≋-trans {𝒫} (proof (≡-refl , ≡-refl , p)) (proof (≡-refl , ≡-refl , q)) = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-trans p q)

≡-to-◇-≋ : {x y : ◇-Fam 𝒫 w} → x ≡ y → x ◇-≋ y
≡-to-◇-≋ ≡-refl = ◇-≋-refl

◇-≋[]-syn : (𝒫 : Psh) → (x y : ◇-Fam 𝒫 w) → Set
◇-≋[]-syn {w = w} 𝒫 = _◇-≋_ {𝒫} {w}

syntax ◇-≋[]-syn 𝒫 x y = x ◇-≋[ 𝒫 ] y

---------------------
-- ◇ 𝒫 is a presheaf
---------------------

◇_ : (𝒫 : Psh) → Psh
◇ 𝒫 = record
         { Fam           = ◇-Fam 𝒫
         ; _≋_           = _◇-≋_
         ; ≋-equiv       = λ _ → ◇-≋-equiv
         ; wk            = wk-◇
         ; wk-pres-≋     = wk-◇-pres-≋
         ; wk-pres-refl  = wk-◇-pres-refl
         ; wk-pres-trans = wk-◇-pres-trans
         }
   where

   ◇-≋-equiv : IsEquivalence (_◇-≋_ {𝒫} {w})
   ◇-≋-equiv = record
     { refl  = ◇-≋-refl
     ; sym   = ◇-≋-sym
     ; trans = ◇-≋-trans
     }

   wk-◇ : w ⊆ w' → ◇-Fam 𝒫 w → ◇-Fam 𝒫 w'
   wk-◇ i (elem (v , r , p)) = elem (factorW i r , factorR i r , wk[ 𝒫 ] (factor⊆ i r) p)

   opaque
     wk-◇-pres-≋ : (i : w ⊆ w') {x y : ◇-Fam 𝒫 w} → x ◇-≋ y → wk-◇ i x ◇-≋ wk-◇ i y
     wk-◇-pres-≋ _i (proof (≡-refl , ≡-refl , p≋p')) = proof (≡-refl , ≡-refl , wk[ 𝒫 ]-pres-≋ _ p≋p')

     wk-◇-pres-refl : (x : ◇-Fam 𝒫 w) → wk-◇ ⊆-refl x ◇-≋ x
     wk-◇-pres-refl (elem (v , r , p)) rewrite factor-pres-⊆-refl r = proof (≡-refl , (≡-refl , wk[ 𝒫 ]-pres-refl p))

     wk-◇-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (x : ◇-Fam 𝒫 w)
       → wk-◇ (⊆-trans i i') x ◇-≋ wk-◇ i' (wk-◇ i x)
     wk-◇-pres-trans i i' (elem (v , r , p)) rewrite factor-pres-⊆-trans i i' r = proof (≡-refl , (≡-refl , wk[ 𝒫 ]-pres-trans _ _ p))

---------------------------
-- ◇ is a presheaf functor
---------------------------

-- made opaque to speedup type-checking and discourage relying on implementation details
opaque
  ◇-map-fun : (f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → ({w : W} → ◇-Fam 𝒫 w → ◇-Fam 𝒬 w)
  ◇-map-fun f (elem (v , r , p)) = elem (v , r , f p)

  ◇-map-fun-pres-≈̇ : {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → (p : ◇-Fam 𝒫 w) → ◇-map-fun (t .apply) p ◇-≋[ 𝒬 ] ◇-map-fun (t' .apply) p
  ◇-map-fun-pres-≈̇ {𝒫} {t = t} {t'} t≈̇t' (elem (v , r , p)) = proof (≡-refl , (≡-refl , apply-≈̇' t≈̇t' ≋[ 𝒫 ]-refl))

  ◇-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◇ 𝒫 →̇ ◇ 𝒬)
  ◇-map_ {𝒫} {𝒬} t = record
    { fun     = ◇-map-fun (t .apply)
    ; pres-≋  = ◇-map-fun-pres-≋ (t .apply-≋)
    ; natural = ◇-map-fun-natural (t .natural)
    }
    where
      opaque
        ◇-map-fun-pres-≋ : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-pres-≋ : Pres-≋ 𝒫 𝒬 f) → Pres-≋ (◇ 𝒫) (◇ 𝒬) (◇-map-fun f)
        ◇-map-fun-pres-≋ f-pres-≋ (proof (≡-refl , ≡-refl , p≋p')) = proof (≡-refl , ≡-refl , f-pres-≋ p≋p')

        ◇-map-fun-natural : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-natural : Natural 𝒫 𝒬 f) → Natural (◇ 𝒫) (◇ 𝒬) (◇-map-fun f)
        ◇-map-fun-natural f-natural i (elem (v , r , p)) = proof (≡-refl , (≡-refl , f-natural _ p))

  ◇-map-pres-≈̇ : {𝒫 𝒬 : Psh} {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → ◇-map t ≈̇ ◇-map t'
  ◇-map-pres-≈̇ {t = t} {t'} t≈̇t' = proof-≈̇ (λ p → ◇-map-fun-pres-≈̇ {t = t} {t'} t≈̇t' p)

  ◇-map-pres-≈̇[_,_] :{𝒫 𝒬 : Psh} (t t' : 𝒫 →̇ 𝒬) → t ≈̇ t' → ◇-map t ≈̇ ◇-map t'
  ◇-map-pres-≈̇[ t , t' ] = ◇-map-pres-≈̇ {t = t} {t'}

  ◇-map-pres-id : {𝒫 : Psh} → ◇-map id'[ 𝒫 ] ≈̇ id'
  ◇-map-pres-id = proof-≈̇ (λ p → ◇-≋-refl)

  ◇-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◇-map (t' ∘' t) ≈̇ ◇-map t' ∘' ◇-map t
  ◇-map-pres-∘ _t' _t = proof-≈̇ (λ p → ◇-≋-refl)
