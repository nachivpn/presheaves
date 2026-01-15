{-# OPTIONS --safe #-}

open import Frame.IFrame
import Frame.CFrame as CF

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Presheaf.Functor.Cover.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  {K    : W → Set}
  {_∈_ : (v : W) {w : W} → K w → Set}
  (let open Core K _∈_)
  (CF : CFrame)
  where

open IFrame IF
open CFrame CF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans ; subst to ≡-subst ; cong to ≡-cong)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)
  
open import Data.Product using (∃; Σ; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import HEUtil

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

ForAllW[_]≋ : (𝒫 : Psh) {k : K w} {k' : K w'} → ForAllW k (𝒫 ₀_) → ForAllW k' (𝒫 ₀_) → Set
ForAllW[ 𝒫 ]≋ {k} {k'} f g = ∀ {v} {p : v ∈ k} {p' : v ∈ k'} → p ≅ p' → f p ≋[ 𝒫 ] g p'

record 𝒞-Fam (𝒫 : Psh) (w : W) : Set where
  constructor elem
  field
    cov   : K w
    elems : ForAllW cov (𝒫 ₀_)

open 𝒞-Fam public

record _𝒞-≋_ {𝒫 : Psh} {w : W} (x y : 𝒞-Fam 𝒫 w) : Set where
  constructor proof
  field
    cov≋   : cov x ≡ cov y
    elems≋ : ForAllW[ 𝒫 ]≋ (elems x) (elems y)

open _𝒞-≋_ public

𝒞-≋[]-syn : (𝒫 : Psh) → (x y : 𝒞-Fam 𝒫 w) → Set
𝒞-≋[]-syn {w = w} 𝒫 = _𝒞-≋_ {𝒫} {w}

syntax 𝒞-≋[]-syn 𝒫 x y = x 𝒞-≋[ 𝒫 ] y

𝒞-≋-refl : {x : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] x
𝒞-≋-refl {𝒫 = 𝒫} {x = x}
  = proof ≡-refl λ p → ≋[ 𝒫 ]-reflexive (≡-cong (elems x) (≅-to-≡ p))

𝒞-≋-sym : {x y : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] y → y 𝒞-≋[ 𝒫 ] x
𝒞-≋-sym {𝒫 = 𝒫} (proof ≡-refl f)
  = proof ≡-refl (λ p → ≋[ 𝒫 ]-sym (f (≅-sym p)))

𝒞-≋-trans : {x y z : 𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] y → y 𝒞-≋[ 𝒫 ] z → x 𝒞-≋[ 𝒫 ] z
𝒞-≋-trans {𝒫 = 𝒫} (proof ≡-refl f) (proof q f')
  = proof q (λ r → ≋[ 𝒫 ]-trans (f ≅-refl) (f' r))

wkElems[_] : (𝒫 : Psh) → {k : K w} {k' : K w'} → k ≼ k' → ForAllW k (𝒫 ₀_) → ForAllW k' (𝒫 ₀_)
wkElems[ 𝒫 ] is fam x = let (_ , x' , i) = is x in wk[ 𝒫 ] i (fam x')

wkElems-pres-≋-left : {k : K w} {k' k'' : K w'} {is : k ≼ k'} {is' : k ≼ k''}
  → is ≋[≼] is' → (elems : ForAllW k (𝒫 ₀_))
  → ForAllW[ 𝒫 ]≋ (wkElems[ 𝒫 ] is elems) (wkElems[ 𝒫 ] is' elems)
wkElems-pres-≋-left {𝒫 = 𝒫} (≡-refl , is≋is') _ {v} {p} {.p} ≅-refl  rewrite is≋is' {v} {p} ≅-refl
  = ≋[ 𝒫 ]-refl

wkElems-pres-≋-right : {k : K w} {k' : K w'}
  → (is : k ≼ k') {elems elems' : ForAllW k (𝒫 ₀_)}
  → ForAllW[ 𝒫 ]≋ elems elems'
  → ForAllW[ 𝒫 ]≋ (wkElems[ 𝒫 ] is elems) (wkElems[ 𝒫 ] is elems')
wkElems-pres-≋-right {𝒫 = 𝒫} is el≋el' ≅-refl
  = wk[ 𝒫 ]-pres-≋ _ (el≋el' ≅-refl)

wkElems-pres-≋ : {k : K w} {k' : K w'} {is is' : k ≼ k'} {elems elems' : ForAllW k (𝒫 ₀_)}
  → is ≋[≼] is'
  → ForAllW[ 𝒫 ]≋ elems elems'
  → ForAllW[ 𝒫 ]≋ (wkElems[ 𝒫 ] is elems) (wkElems[ 𝒫 ] is' elems')
wkElems-pres-≋ {𝒫 = 𝒫} (≡-refl , ref≋) el≋el' {v} {p} {.p} ≅-refl
  rewrite ref≋ {v} {p} ≅-refl = wk[ 𝒫 ]-pres-≋ _ (el≋el' ≅-refl)

𝒞-kmap : w ⇒≼ w' → 𝒞-Fam 𝒫 w → 𝒞-Fam 𝒫 w'
𝒞-kmap {𝒫 = 𝒫} h (elem k fam) = elem (h $α k) (wkElems[ 𝒫 ] (h $≼ k) fam)

𝒞-kmap-pres-≋-left : {h h' : w ⇒≼ w'} → h ≋[⇒≼] h' → (x : 𝒞-Fam 𝒫 w) → 𝒞-kmap h x 𝒞-≋[ 𝒫 ] 𝒞-kmap h' x
𝒞-kmap-pres-≋-left {𝒫 = 𝒫} {h = h} {h'} h≋h' (elem k elems)
  = let (k1≡k2 , is1≋is2) = h≋h' k in proof k1≡k2 (wkElems-pres-≋-left {𝒫 = 𝒫} is1≋is2 elems)
  
𝒞-kmap-pres-≋-right : (h : w ⇒≼ w') {x x' :  𝒞-Fam 𝒫 w} → x 𝒞-≋[ 𝒫 ] x' → 𝒞-kmap h x 𝒞-≋[ 𝒫 ] 𝒞-kmap h x'
𝒞-kmap-pres-≋-right {𝒫 = 𝒫} h (proof ≡-refl elems≋)= proof ≡-refl λ { ≅-refl → wk[ 𝒫 ]-pres-≋ _ (elems≋ ≅-refl) }

𝒞-kmap-pres-refl : (x : 𝒞-Fam 𝒫 w) → 𝒞-kmap ⇒≼-refl[ w ] x 𝒞-≋ x
𝒞-kmap-pres-refl {𝒫 = 𝒫} x = proof ≡-refl λ { {_} {p} ≅-refl → wk[ 𝒫 ]-pres-refl (x .elems p)}

𝒞-kmap-pres-trans : (h : w ⇒≼ w') (h' : w' ⇒≼ w'') (x : 𝒞-Fam 𝒫 w) → 𝒞-kmap (⇒≼-trans h h') x 𝒞-≋ 𝒞-kmap h' (𝒞-kmap h x)
𝒞-kmap-pres-trans {𝒫 = 𝒫} h h' x = proof ≡-refl λ { {_} {p} ≅-refl → wk[ 𝒫 ]-pres-trans _ _ _ }

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
   wk-𝒞 i cp = 𝒞-kmap (refine i) cp

   opaque
     wk-𝒞-pres-≋ : (i : w ⊆ w') {x y : 𝒞-Fam 𝒫 w} → x 𝒞-≋ y → wk-𝒞 i x 𝒞-≋ wk-𝒞 i y
     wk-𝒞-pres-≋ i p = 𝒞-kmap-pres-≋-right (refine i) p

     wk-𝒞-pres-refl : (x : 𝒞-Fam 𝒫 w) → wk-𝒞 ⊆-refl x 𝒞-≋ x
     wk-𝒞-pres-refl x = 𝒞-≋-trans (𝒞-kmap-pres-≋-left refine-pres-⇒≼-refl x) (𝒞-kmap-pres-refl x)

     wk-𝒞-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (x : 𝒞-Fam 𝒫 w)
       → wk-𝒞 (⊆-trans i i') x 𝒞-≋ wk-𝒞 i' (wk-𝒞 i x)
     wk-𝒞-pres-trans i i' x = 𝒞-≋-trans (𝒞-kmap-pres-≋-left (refine-pres-⇒≼-trans i i') x) (𝒞-kmap-pres-trans (refine i) (refine i') x)

---------------------------
-- 𝒞 is a presheaf functor
---------------------------

open import Function using (_∘_)

-- made opaque to speedup type-checking and discourage relying on implementation details
opaque
  𝒞-map-fun : (f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → ({w : W} → 𝒞-Fam 𝒫 w → 𝒞-Fam 𝒬 w)
  𝒞-map-fun f (elem k fam) = elem k (f ∘ fam)

  𝒞-map-fun-pres-≈̇ : {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → (p : 𝒞-Fam 𝒫 w) → 𝒞-map-fun (t .apply) p 𝒞-≋[ 𝒬 ] 𝒞-map-fun (t' .apply) p
  𝒞-map-fun-pres-≈̇ {𝒫} t≈̇t' (elem k fam) = proof ≡-refl λ { ≅-refl → apply-≈̇' t≈̇t' ≋[ 𝒫 ]-refl }

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
        𝒞-map-fun-natural f-natural i (elem k fam) = proof ≡-refl λ { ≅-refl → f-natural _ _ }

  𝒞-map-pres-≈̇ : {𝒫 𝒬 : Psh} {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → 𝒞-map t ≈̇ 𝒞-map t'
  𝒞-map-pres-≈̇ {t = t} {t'} t≈̇t' = proof-≈̇ (λ p → 𝒞-map-fun-pres-≈̇ {t = t} {t'} t≈̇t' p)

  𝒞-map-pres-≈̇[_,_] :{𝒫 𝒬 : Psh} (t t' : 𝒫 →̇ 𝒬) → t ≈̇ t' → 𝒞-map t ≈̇ 𝒞-map t'
  𝒞-map-pres-≈̇[ t , t' ] = 𝒞-map-pres-≈̇ {t = t} {t'}

  𝒞-map-pres-id : {𝒫 : Psh} → 𝒞-map id'[ 𝒫 ] ≈̇ id'
  𝒞-map-pres-id = proof-≈̇ (λ p → 𝒞-≋-refl)

  𝒞-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → 𝒞-map (t' ∘' t) ≈̇ 𝒞-map t' ∘' 𝒞-map t
  𝒞-map-pres-∘ _t' _t = proof-≈̇ (λ p → 𝒞-≋-refl)
