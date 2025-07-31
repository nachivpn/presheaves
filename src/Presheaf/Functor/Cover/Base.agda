{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.CFrame as CF

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Presheaf.Functor.Cover.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (𝒦   : KPsh)
  (let open KPsh 𝒦)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core 𝒦 _∈_)
  (CF : CFrame)
  where

open IFrame IF
open CFrame CF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product using (∃; Σ; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

record 𝒞-Fam (𝒫 : Psh) (w : W) : Set where
  constructor elem
  field
    cov : K w
    fam : ForAllW cov (𝒫 ₀_)

open 𝒞-Fam public

record _𝒞-≋_ {𝒫 : Psh} {w : W} (x y : 𝒞-Fam 𝒫 w) : Set where
  constructor proof
  field
    cov≋ : cov x ≡ cov y
    fam≋ : ForAll∈ (cov x) λ p → fam x p ≋[ 𝒫 ] (fam y (subst (_ ∈_) cov≋ p))

𝒞-≋[]-syn : (𝒫 : Psh) → (x y : 𝒞-Fam 𝒫 w) → Set
𝒞-≋[]-syn {w = w} 𝒫 = _𝒞-≋_ {𝒫} {w}

syntax 𝒞-≋[]-syn 𝒫 x y = x 𝒞-≋[ 𝒫 ] y

𝒞-≋-refl : {x : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] x
𝒞-≋-refl {𝒫 = 𝒫}
  = proof ≡-refl (λ p → ≋[ 𝒫 ]-refl)

𝒞-≋-sym : {x y : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] y → y 𝒞-≋[ 𝒫 ] x
𝒞-≋-sym {𝒫 = 𝒫} (proof ≡-refl f)
  = proof ≡-refl (λ p → ≋[ 𝒫 ]-sym (f p))

𝒞-≋-trans : {x y z : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] y → y 𝒞-≋[ 𝒫 ] z → x 𝒞-≋[ 𝒫 ] z
𝒞-≋-trans {𝒫 = 𝒫} (proof ≡-refl f) (proof ≡-refl f')
  = proof ≡-refl (λ p → ≋[ 𝒫 ]-trans (f p) (f' p))

---------------------
-- 𝒞 𝒫 is a presheaf
---------------------

𝒞_ : (𝒫 : Psh) → Psh
𝒞 𝒫 = record
         { Fam           = 𝒞-Fam 𝒫
         ; _≋_           = _𝒞-≋_
         ; ≋-equiv       = λ _ → 𝒞-≋-equiv
         ; wk            = wk-𝒞
         ; wk-pres-≋     = wk-𝒞-pres-≋
         ; wk-pres-refl  = wk-𝒞-pres-refl
         ; wk-pres-trans = wk-𝒞-pres-trans
         }
   where

   𝒞-≋-equiv : IsEquivalence (_𝒞-≋_ {𝒫} {w})
   𝒞-≋-equiv = record
     { refl  = 𝒞-≋-refl
     ; sym   = 𝒞-≋-sym
     ; trans = 𝒞-≋-trans
     }

   wk-𝒞 : w ⊆ w' → 𝒞-Fam 𝒫 w → 𝒞-Fam 𝒫 w'
   wk-𝒞 i (elem k f) = elem (wkK i k) (λ p → wk[ 𝒫 ] (factor⊆ i k p) (f (factor∈ i k p)))

   opaque
     wk-𝒞-pres-≋ : (i : w ⊆ w') {x y : 𝒞-Fam 𝒫 w} → x 𝒞-≋ y → wk-𝒞 i x 𝒞-≋ wk-𝒞 i y
     wk-𝒞-pres-≋ i (proof ≡-refl g) = proof ≡-refl (λ p → wk[ 𝒫 ]-pres-≋ _ (g (factor∈ i _ p)))

     wk-𝒞-pres-refl : (x : 𝒞-Fam 𝒫 w) → wk-𝒞 ⊆-refl x 𝒞-≋ x
     wk-𝒞-pres-refl (elem k f) = proof (wkK-pres-refl k) wk-𝒞-fam-pres-refl
       where
       wk-𝒞-fam-pres-refl :  (p : v ∈ wkK ⊆-refl k) →
         wk[ 𝒫 ] (factor⊆ ⊆-refl k p) (f (factor∈ ⊆-refl k p))
           ≋[ 𝒫 ] (f (subst (_∈_ v) (wkK-pres-refl k) p))
       wk-𝒞-fam-pres-refl p rewrite factor-pres-refl k p | wkK-pres-refl k = wk[ 𝒫 ]-pres-refl (f p)

     wk-𝒞-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (x : 𝒞-Fam 𝒫 w)
       → wk-𝒞 (⊆-trans i i') x 𝒞-≋ wk-𝒞 i' (wk-𝒞 i x)
     wk-𝒞-pres-trans i i' (elem k f) = proof (wkK-pres-trans i i' k) wk-𝒞-fam-pres-trans
       where
       wk-𝒞-fam-pres-trans : (p : v ∈ wkK (⊆-trans i i') k) →
         wk[ 𝒫 ] (factor⊆ (⊆-trans i i') k p) (f (factor∈ (⊆-trans i i') k p))
           ≋[ 𝒫 ] ((wk-𝒞 i' (wk-𝒞 i (elem k f)) .fam) (subst (v ∈_) (wkK-pres-trans i i' k) p))
       wk-𝒞-fam-pres-trans p rewrite factor-pres-trans i i' k p | wkK-pres-trans i i' k = wk[ 𝒫 ]-pres-trans _ _ (f _)

---------------------------
-- 𝒞 is a presheaf functor
---------------------------

open import Function using (_∘_)

-- made opaque to speedup type-checking and discourage relying on implementation details
opaque
  𝒞-map-fun : (f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → ({w : W} → 𝒞-Fam 𝒫 w → 𝒞-Fam 𝒬 w)
  𝒞-map-fun f (elem k fam) = elem k (f ∘ fam)

  𝒞-map-fun-pres-≈̇ : {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → (p : 𝒞-Fam 𝒫 w) → 𝒞-map-fun (t .apply) p 𝒞-≋[ 𝒬 ] 𝒞-map-fun (t' .apply) p
  𝒞-map-fun-pres-≈̇ {𝒫} t≈̇t' (elem k fam) = proof ≡-refl (λ p → apply-≈̇' t≈̇t' ≋[ 𝒫 ]-refl)

  𝒞-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (𝒞 𝒫 →̇ 𝒞 𝒬)
  𝒞-map_ {𝒫} {𝒬} t = record
    { fun     = 𝒞-map-fun (t .apply)
    ; pres-≋  = 𝒞-map-fun-pres-≋ (t .apply-≋)
    ; natural = 𝒞-map-fun-natural (t .natural)
    }
    where
      opaque
        𝒞-map-fun-pres-≋ : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-pres-≋ : Pres-≋ 𝒫 𝒬 f) → Pres-≋ (𝒞 𝒫) (𝒞 𝒬) (𝒞-map-fun f)
        𝒞-map-fun-pres-≋ f-pres-≋ (proof ≡-refl fam≋) = proof ≡-refl (f-pres-≋ ∘ fam≋)

        𝒞-map-fun-natural : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-natural : Natural 𝒫 𝒬 f) → Natural (𝒞 𝒫) (𝒞 𝒬) (𝒞-map-fun f)
        𝒞-map-fun-natural f-natural i (elem k fam) = proof ≡-refl λ p → f-natural (factor⊆ i k p) (fam (factor∈ i k p))

  𝒞-map-pres-≈̇ : {𝒫 𝒬 : Psh} {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → 𝒞-map t ≈̇ 𝒞-map t'
  𝒞-map-pres-≈̇ {t = t} {t'} t≈̇t' = proof-≈̇ (λ p → 𝒞-map-fun-pres-≈̇ {t = t} {t'} t≈̇t' p)

  𝒞-map-pres-≈̇[_,_] :{𝒫 𝒬 : Psh} (t t' : 𝒫 →̇ 𝒬) → t ≈̇ t' → 𝒞-map t ≈̇ 𝒞-map t'
  𝒞-map-pres-≈̇[ t , t' ] = 𝒞-map-pres-≈̇ {t = t} {t'}

  𝒞-map-pres-id : {𝒫 : Psh} → 𝒞-map id'[ 𝒫 ] ≈̇ id'
  𝒞-map-pres-id = proof-≈̇ (λ p → 𝒞-≋-refl)

  𝒞-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → 𝒞-map (t' ∘' t) ≈̇ 𝒞-map t' ∘' 𝒞-map t
  𝒞-map-pres-∘ _t' _t = proof-≈̇ (λ p → 𝒞-≋-refl)
