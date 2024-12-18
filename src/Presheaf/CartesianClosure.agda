{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

module Presheaf.CartesianClosure
  {W   : Set}
  {_⊆_ : (Γ Γ' : W) → Set}
  (IF  : IFrame W _⊆_)
  (let open IFrame IF)
  where

open import Presheaf.Base IF

open import Function using (id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Data.Unit using (⊤; tt)
open import Data.Unit.Properties using () renaming (⊤-irrelevant to ⊤-eta)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning 

private
  variable
    w v              : W
    i i' i''         : w ⊆ v
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' : Psh
    s s' t t' u u'   : 𝒫 →̇ 𝒬

--
-- Cartesian products
--

Unit' : Psh
Unit' = record
  { Fam           = λ _w → ⊤
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _w → ≡-equiv
  ; wk            = λ _i → id
  ; wk-pres-≋     = λ _i → cong id
  ; wk-pres-refl  = λ _x → ≡-refl
  ; wk-pres-trans = λ _x _i _i' → ≡-refl
  }

[]' = Unit'

unit' : ℛ →̇ Unit'
unit' = record
  { fun     = λ _r → tt
  ; pres-≋  = λ {w} _p≋p' → ≋[ Unit' ]-refl {w}
  ; natural = λ {_w} {v} _i _r → ≋[ Unit' ]-refl {v}
  }

unit'[_] = λ ℛ → unit' {ℛ}

Unit'-eta : t ≈̇ unit'
Unit'-eta {ℛ} {t} = record { proof = λ r → ⊤-eta (t .apply r) (unit'[ ℛ ] .apply r) }

[]'-eta = Unit'-eta

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record Fam (w : W) : Set where
    constructor elem
    field
      pair : P w × Q w

  record _≋_ {w : W} (x y : Fam w) : Set where
    constructor proof
    field
      proof : let elem (p , q) = x; elem (p' , q') = y in p ≋[ 𝒫 ] p' × q ≋[ 𝒬 ] q'

  private
    ≋-equiv : ∀ (w : W) → IsEquivalence (_≋_ {w})
    ≋-equiv _w = record
      { refl  = proof (≋[ 𝒫 ]-refl , ≋[ 𝒬 ]-refl)
      ; sym   = λ (proof (p≋p' , q≋q')) → proof (≋[ 𝒫 ]-sym p≋p' , ≋[ 𝒬 ]-sym q≋q')
      ; trans = λ (proof (p≋p' , q≋q')) (proof (p'≋p'' , q'≋q'')) → proof (≋[ 𝒫 ]-trans p≋p' p'≋p'' , ≋[ 𝒬 ]-trans q≋q' q'≋q'')
      }

  _×'_ : Psh
  _×'_ = record
    { Fam           = Fam
    ; _≋_           = _≋_
    ; ≋-equiv       = ≋-equiv
    ; wk            = λ i (elem (p , q)) → elem (wk[ 𝒫 ] i p , wk[ 𝒬 ] i q)
    ; wk-pres-≋     = λ i (proof (p≋p' , q≋q')) → proof (wk[ 𝒫 ]-pres-≋ i p≋p' , wk[ 𝒬 ]-pres-≋ i q≋q')
    ; wk-pres-refl  = λ (elem (p , q)) → proof (wk[ 𝒫 ]-pres-refl p , wk[ 𝒬 ]-pres-refl q)
    ; wk-pres-trans = λ i i' (elem (p , q)) → proof (wk[ 𝒫 ]-pres-trans i i' p , wk[ 𝒬 ]-pres-trans i i' q)
    }

module _ {𝒫 𝒬 : Psh} where
  π₁' : 𝒫 ×' 𝒬 →̇ 𝒫
  π₁' = record
    { fun     = λ x → let elem (p , _q) = x in p
    ; pres-≋  = λ x≋y → let proof (p≋p' , _q≋q') = x≋y in p≋p'
    ; natural = λ _i x → let elem (_p , _q) = x in ≋[ 𝒫 ]-refl
    }

  π₂' : 𝒫 ×' 𝒬 →̇ 𝒬
  π₂' = record
    { fun     = λ x → let elem (_p , q) = x in q
    ; pres-≋  = λ x≋y → let proof (_p≋p' , q≋q') = x≋y in q≋q'
    ; natural = λ _i x → let elem (_p , _q) = x in ≋[ 𝒬 ]-refl
    }

  fst' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒫
  fst' = π₁' ∘_

  snd' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒬
  snd' = π₂' ∘_

  pair' : (t : ℛ →̇ 𝒫) → (u : ℛ →̇ 𝒬) → ℛ →̇ 𝒫 ×' 𝒬
  pair' t u = record
    { fun     = λ r → elem (t .apply r , u .apply r)
    ; pres-≋  = λ r≋r' → proof (t .apply-≋ r≋r' , u .apply-≋ r≋r')
    ; natural = λ i r → proof (t .natural i r , u .natural i r)
    }

  ⟨_,_⟩' = pair'

  opaque
    pair'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → pair' t u ≈̇ pair' t' u'
    pair'-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ r → proof (t≈̇t' .apply-≋ r , u≈̇u' .apply-≋ r) }

    pair'-pres-≈̇-left : t ≈̇ t' → pair' t u ≈̇ pair' t' u
    pair'-pres-≈̇-left {u = u} t≈̇t' = pair'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    pair'-pres-≈̇-right : u ≈̇ u' → pair' t u ≈̇ pair' t u'
    pair'-pres-≈̇-right {t = t} u≈̇u' = pair'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    pair'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → pair' t u ∘ s ≈̇ pair' (t ∘ s) (u ∘ s)
    pair'-nat _t _u _s = ≈̇-refl

    ×'-beta-left : ∀ {t : ℛ →̇ 𝒫} (u : ℛ →̇ 𝒬) → fst' (pair' t u) ≈̇ t
    ×'-beta-left {_t} _u = record { proof = λ _r → ≋[ 𝒫 ]-refl }

    ×'-beta-right : ∀ (t : ℛ →̇ 𝒫) {u : ℛ →̇ 𝒬} → snd' (pair' t u) ≈̇ u
    ×'-beta-right t {_u} = record { proof = λ _r → ≋[ 𝒬 ]-refl }

    ×'-eta : t ≈̇ pair' (fst' t) (snd' t)
    ×'-eta = record { proof = λ _r → ≋[ 𝒫 ×' 𝒬 ]-refl }

π₁'[_] = λ {𝒫} 𝒬 → π₁' {𝒫} {𝒬}

π₁'[_][_] = λ 𝒫 𝒬 → π₁' {𝒫} {𝒬}

π₂'[_] = λ 𝒫 {𝒬} → π₂' {𝒫} {𝒬}

π₂'[_][_] = λ 𝒫 𝒬 → π₂' {𝒫} {𝒬}

_×'-map_ : (t : 𝒫 →̇ 𝒫') → (u : 𝒬 →̇ 𝒬') → 𝒫 ×' 𝒬 →̇ 𝒫' ×' 𝒬'
_×'-map_ {𝒫 = 𝒫} {𝒬 = 𝒬} t u = pair' (t ∘ π₁'[ 𝒬 ]) (u ∘ π₂'[ 𝒫 ])

assoc' : (𝒫 ×' 𝒬) ×' ℛ →̇ 𝒫 ×' (𝒬 ×' ℛ)
assoc' = ⟨ π₁' ∘ π₁' , ⟨ π₂' ∘ π₁' , π₂' ⟩' ⟩'

opaque
  ×'-map-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → t ×'-map u ≈̇ t' ×'-map u'
  ×'-map-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ x → let elem (p , q) = x in proof (t≈̇t' .apply-≋ p , u≈̇u' .apply-≋ q) }

  ×'-map-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : 𝒬 →̇ 𝒬') → t ×'-map u ≈̇ t' ×'-map u
  ×'-map-pres-≈̇-left t≈̇t' u = ×'-map-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

  ×'-map-pres-≈̇-right : ∀ (t : 𝒫 →̇ 𝒫') (_ : u ≈̇ u') → t ×'-map u ≈̇ t ×'-map u'
  ×'-map-pres-≈̇-right t u≈̇u' = ×'-map-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

  ×'-map-pres-id : ∀ {𝒫 𝒬 : Psh} → id'[ 𝒫 ] ×'-map id'[ 𝒬 ] ≈̇ id'[ 𝒫 ×' 𝒬 ]
  ×'-map-pres-id {𝒫} {𝒬} = record { proof = λ _x → ≋[ 𝒫 ×' 𝒬 ]-refl }

--
-- Exponentials
--

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record →'-Fam (w : W) : Set where
    constructor elem
    field
      fun     : {w' : W} → (i : w ⊆ w') → P w' → Q w'
      pres-≋  : ∀ {w' : W} → (i : w ⊆ w') {p p' : P w'} → (p≋p' : p ≋[ 𝒫 ] p') → fun i p ≋[ 𝒬 ] fun i p'
      natural : ∀ {w' w'' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (p : P w') → wk[ 𝒬 ] i' (fun i p) ≋[ 𝒬 ] fun (⊆-trans i i') (wk[ 𝒫 ] i' p)

  open →'-Fam using (natural) renaming (fun to apply; pres-≋ to apply-≋) public

  record _→'-≋_ {w : W} (f g : →'-Fam w) : Set where
    constructor proof
    field
      pw : ∀ {v : W} (i : w ⊆ v) (p : P v) → f .apply i p ≋[ 𝒬 ] g .apply i p

  open _→'-≋_ using (pw) public

  private
    →'-≋-equiv : ∀ (_w : W) → IsEquivalence (_→'-≋_ {_w})
    →'-≋-equiv _w = record
      { refl  = proof (λ _i _p → ≋[ 𝒬 ]-refl)
      ; sym   = λ {f} {g} f≋g → proof (λ i p → ≋[ 𝒬 ]-sym (f≋g .pw i p))
      ; trans = λ {f} {g} {h} f≋g g≋h → proof (λ i p → ≋[ 𝒬 ]-trans (f≋g .pw i p) (g≋h .pw i p))
      }

  _→'_ : Psh
  _→'_ = record
    { Fam           = →'-Fam
    ; _≋_           = _→'-≋_
    ; wk            = λ i f → elem (λ i' p → f .apply (⊆-trans i i') p)
                                   (λ i' p≋p' → f .apply-≋ (⊆-trans i i') p≋p')
                                   (λ i' i'' p → subst (λ hole → wk[ 𝒬 ] i'' (f .apply (⊆-trans i i') p) ≋[ 𝒬 ] f .apply hole (wk[ 𝒫 ] i'' p)) (⊆-trans-assoc i i' i'') (f .natural (⊆-trans i i') i'' p))
    ; ≋-equiv       = →'-≋-equiv
    ; wk-pres-≋     = λ i f≋g → proof (λ i' → f≋g .pw (⊆-trans i i'))
    ; wk-pres-refl  = λ f → proof (λ i p → ≋[ 𝒬 ]-reflexive (cong (λ hole → f .apply hole p) (⊆-trans-unit-left i)))
    ; wk-pres-trans = λ i i' f → proof (λ i'' p → ≋[ 𝒬 ]-reflexive˘ (cong (λ hole → f .apply hole p) (≡-sym (⊆-trans-assoc i i' i''))))
    }

module _ {𝒫 𝒬 : Psh} where
  private
    →'-≋-apply-sq : ∀ {f g : 𝒫 →' 𝒬 ₀ w} (_f≋g : f ≋[ 𝒫 →' 𝒬 ] g) (i : w ⊆ v) {p p' : 𝒫 ₀ v} → (_p≋p' : p ≋[ 𝒫 ] p') → f .apply i p ≋[ 𝒬 ] g .apply i p'
    →'-≋-apply-sq {_w} {_v} {f} {g} f≋g i {p} {p'} p≋p' = let open EqReasoning ≋[ 𝒬 ]-setoid in begin
      f .apply i p   ≈⟨ f .apply-≋ i p≋p' ⟩
      f .apply i p'  ≈⟨ f≋g .pw i p' ⟩
      g .apply i p'  ∎

  app' : (t : ℛ →̇ 𝒫 →' 𝒬) → (u : ℛ →̇ 𝒫) → ℛ →̇ 𝒬
  app' {ℛ} t u = record
    { fun     = λ r → t .apply r .apply ⊆-refl (u .apply r)
    ; pres-≋  = λ r≋r' → →'-≋-apply-sq (t .apply-≋ r≋r') ⊆-refl (u .apply-≋ r≋r')
    ; natural = λ i r → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
        wk[ 𝒬 ] i (t .apply r .apply ⊆-refl (u .apply r))                   ≈⟨ t .apply r .natural ⊆-refl i (u .apply r) ⟩
        t .apply r .apply (⊆-trans ⊆-refl i) (wk[ 𝒫 ] i (u .apply r))       ≈⟨ t .apply r .apply-≋ (⊆-trans ⊆-refl i) (u .natural i r) ⟩
        t .apply r .apply (⊆-trans ⊆-refl i) (u .apply (wk[ ℛ ] i r))       ≡⟨ cong (λ hole → t .apply r .apply hole (u .apply (wk[ ℛ ] i r))) (⊆-trans-unit-left i) ⟩
        t .apply r .apply i                  (u .apply (wk[ ℛ ] i r))       ≡˘⟨ cong (λ hole → t .apply r .apply hole (u .apply (wk[ ℛ ] i r))) (⊆-trans-unit-right i) ⟩
        t .apply r .apply (⊆-trans i ⊆-refl) (u .apply (wk[ ℛ ] i r))       ≡⟨⟩
        wk[ 𝒫 →' 𝒬 ] i (t .apply r) .apply ⊆-refl (u .apply (wk[ ℛ ] i r))  ≈⟨ t .natural i r .pw ⊆-refl (u .apply (wk[ ℛ ] i r)) ⟩
        t .apply (wk[ ℛ ] i r) .apply ⊆-refl (u .apply (wk[ ℛ ] i r))       ∎
    }

  opaque
    app'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → app' t u ≈̇ app' t' u'
    app'-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ r → →'-≋-apply-sq (t≈̇t' .apply-≋ r) ⊆-refl (u≈̇u' .apply-≋ r) }

    app'-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : ℛ →̇ 𝒫) → app' t u ≈̇ app' t' u
    app'-pres-≈̇-left t≈̇t' u = app'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    app'-pres-≈̇-right : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) (_ : u ≈̇ u') → app' t u ≈̇ app' t u'
    app'-pres-≈̇-right t u≈̇u' = app'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    app'-nat : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) (u : ℛ →̇ 𝒫) (s : ℛ' →̇ ℛ) → app' t u ∘ s ≈̇ app' (t ∘ s) (u ∘ s)
    app'-nat _t _u _s = record { proof = λ _r' → ≋[ 𝒬 ]-refl }

lam' : (t : ℛ ×' 𝒫 →̇ 𝒬) → ℛ →̇ 𝒫 →' 𝒬
lam' {ℛ} {𝒫} {𝒬} t = record
  { fun     = λ r → record
                { fun     = λ i p → t .apply (elem (wk[ ℛ ] i r , p))
                ; pres-≋  = λ i p≋p' → t .apply-≋ (proof (≋[ ℛ ]-refl , p≋p'))
                ; natural = λ i i' p → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
                    wk[ 𝒬 ] i' (t .apply (elem (wk[ ℛ ] i r , p)))             ≈⟨ t .natural i' (elem (wk[ ℛ ] i r , p)) ⟩
                    t .apply (elem (wk[ ℛ ] i' (wk[ ℛ ] i r) , wk[ 𝒫 ] i' p))  ≈˘⟨ t .apply-≋ (proof (wk[ ℛ ]-pres-trans i i' r , ≋[ 𝒫 ]-refl)) ⟩
                    t .apply (elem (wk[ ℛ ] (⊆-trans i i') r , wk[ 𝒫 ] i' p))  ∎
                }
  ; pres-≋  = λ r≋r' → proof λ i p → t .apply-≋ (proof (wk[ ℛ ]-pres-≋ i r≋r' , ≋[ 𝒫 ]-refl))
  ; natural = λ i r → proof λ i' p → t .apply-≋ (proof ((wk[ ℛ ]-pres-trans i i' r) , ≋[ 𝒫 ]-refl))
  }

opaque
  lam'-pres-≈̇ : t ≈̇ t' → lam' t ≈̇ lam' t'
  lam'-pres-≈̇ {_𝒬} {ℛ} {𝒫} t≈̇t' = record { proof = λ r → proof (λ i p → t≈̇t' .apply-≋ (elem (wk[ ℛ ] i r , p))) }

  lam'-nat : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (s : ℛ' →̇ ℛ) → lam' t ∘ s ≈̇ lam' (t ∘ s ×'-map id'[ 𝒫 ])
  lam'-nat {_ℛ} {𝒫} {_𝒬} {_ℛ'} t s = record { proof = λ r' → proof (λ i p → t .apply-≋ (proof ((s .natural i r') , ≋[ 𝒫 ]-refl))) }

  →'-beta : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (u : ℛ →̇ 𝒫) → app' (lam' t) u ≈̇ t [ pair' id' u ]'
  →'-beta {ℛ} {𝒫} t u = record { proof = λ r → t .apply-≋ (proof (wk[ ℛ ]-pres-refl r , ≋[ 𝒫 ]-refl)) }

  →'-eta : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) → t ≈̇ lam' {𝒬 = 𝒬} (app' (t [ π₁'[ 𝒫 ] ]') π₂'[ ℛ ])
  →'-eta {ℛ} {𝒫} {𝒬} t = record
    { proof = λ r → proof (λ i p → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
                             t .apply r .apply i p                        ≡˘⟨ cong (λ hole → t .apply r .apply hole p) (⊆-trans-unit-right i) ⟩
                             t .apply r .apply (⊆-trans i ⊆-refl) p       ≡⟨⟩
                             wk[ 𝒫 →' 𝒬 ] i (t .apply r) .apply ⊆-refl p  ≈⟨ t .natural i r .pw ⊆-refl p ⟩
                             t .apply (wk[ ℛ ] i r) .apply ⊆-refl p       ∎
                          )
    }
